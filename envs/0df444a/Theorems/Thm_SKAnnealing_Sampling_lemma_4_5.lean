-- Prove2me | Theorems.Thm_SKAnnealing_Sampling_lemma_4_5
-- name    : SKAnnealing.Sampling.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:42.193199+00:00
-- url     : https://prove2.me/theorems/e14e5f68-e759-4ce0-a0a3-60c38c31dac7
-- title:
--   Lemma 4.5, p. 16 — diagonal terms: $(K\mathbf{Cov}-\mathrm{Id})_{ii}=\lambda_iv_i-\frac{2\beta^2m_i}N(\mathbf{Cov}\,m)_i$, $\max_i|\lambda_i|\le N^{-1/4}$ w.h.p., and the $2\beta^2$ bound
-- statement:
--   Throughout, $0<\beta<1$, $W\sim\mathrm{GOE}(N)$, $x\sim\mathrm{Unif}\{\pm1\}^N$ and $g\sim\mathcal N(0,\mathrm{Id})$ are independent, $\mu_t$ is the measure of Theorem 1.4, $\mathbf{Cov}=\mathbf{Cov}(\mu_t)$, and $K$, $m$, $v_i$, $q_N$, $d_i$, $\lambda_i$, $f_i$ are the TAP quantities (8) at $\mu_t$, with $M=W+\frac\beta Nxx^\top$ (diagonal zeroed).
--
--   **Lemma 4.5 (Diagonal terms).**
--   1. For every $i\in[N]$,
--   $$(K\mathbf{Cov}-\mathrm{Id})_{ii}=\lambda_iv_i-\frac{2\beta^2m_i}N(\mathbf{Cov}\,m)_i .$$
--   2. For every $T>0$ and $a>0$ there are $C$ and $N_0$ such that for all $N\ge N_0$ and $t\in(0,T]$,
--   $$\Pr\Big[\max_{i\in[N]}|\lambda_i|>N^{-1/4}\Big]\le C\,N^{-a}.$$
--   3. Hence, for every $i\in[N]$,
--   $$\big|(K\mathbf{Cov}-\mathrm{Id})_{ii}-\lambda_iv_i\big|\le2\beta^2 .$$
--
--   Parts 1 and 3 are deterministic and hold for every $W$, $x$, $g$ and every real $\beta$, $t$. They control the diagonal of $K\mathbf{Cov}-\mathrm{Id}$ in the proof of Lemma 4.1; part 2 shows the diagonal correction $D=\mathrm{diag}(\lambda_i)$ is $o(1)$.
--
--   Differences from the source:
--   - generalization: parts (i) and (iii) in the setting 0 < β < 1, t > 0 bounded → parts (i) and (iii) for every N, every real β and t, and every W, x, g; reason: they are deterministic consequences of (8), Cov_ii = v_i, |m_i| ≤ 1 and |Cov_ij| ≤ 1, which hold for every full-support law; the printed setting is a special case
--   - reading: fix t > 0 bounded, possibly decaying with N → one N₀ and one constant serve every t ∈ (0, T], for every T > 0; reason: a bound uniform over t ∈ (0, T] is equivalent to the bound for every sequence t_N ∈ (0, T], which is what "possibly decaying with N" requires (reading R5)
--   - encoding: Pr[max_i |λ_i| > N^{−1/4}] ⩽ O(N^{−a}) → ∃ C, N₀ such that for every N ≥ N₀ the measure of the failure event is ≤ C·N^{−a}; reason: O(·) is a constant; the probability is written as the bound on the bad set (reading R4)
--   - encoding: W ∼ GOE(N), a symmetric matrix with diagonal entries → the off-diagonal entries W_{ik}, i < k, iid N(0, 1/N) (OAI.CriticalSK.disorderLaw); no diagonal; reason: σ_i² = 1, so the diagonal only adds a constant to the Hamiltonian and changes no Gibbs measure, kernel or covariance (reading R8)
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 4.5, p. 16 (PDF p. 18)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKAnnealing_Sampling_plantedTilted
import Definitions.Def_SKAnnealing_Sampling_tapHessian

open OAI.CriticalSK MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKAnnealing.Sampling

/-- **Lemma 4.5** (diagonal terms). (i) `(K Cov − Id)_{ii} = λ_i v_i − (2β² m_i/N)(Cov m)_i`.
(ii) For every `a > 0`, `Pr[max_{i ∈ [N]} |λ_i| > N^{−1/4}] ≤ O(N^{−a})`.
(iii) Hence `max_{i ∈ [N]} |(K Cov − Id)_{ii} − λ_i v_i| ≤ 2β²`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Lemma 4.5, p. 16 (PDF p. 18).

**Formalization Note** Clauses (i) and (iii) are deterministic and are stated for every `N`, `β`, `t`, `W`, `x`,
`g` and `i` (generalization: the printed setting `0 < β < 1`, `t > 0` is a special case). Clause (ii) is in the
standing setting of Section 4 (`0 < β < 1`, uniformly over `t ∈ (0, T]` for `N ≥ N₀`, readings R4–R5);
`O(N^{−a})` is `C · N^{−a}`. `Cov m` is `Matrix.mulVec (lawCov µ) m`. -/
theorem lemma_4_5 :
    (∀ (N : ℕ) (β t : ℝ) (W : Disorder N) (x : Spin N) (g : Fin N → ℝ) (i : Fin N),
      let M := plantedMatrix β W x
      let μ := plantedTilted β t W x g
      (tapHessian β M μ * lawCov μ - 1) i i =
        cavityLam β M μ i * tapVar μ i
          - 2 * β ^ 2 * tapMean μ i / N * Matrix.mulVec (lawCov μ) (tapMean μ) i) ∧
    (∀ β : ℝ, 0 < β → β < 1 → ∀ T : ℝ, 0 < T → ∀ a : ℝ, 0 < a →
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ, 0 < t → t ≤ T →
        plantedFieldLaw N {ω | ∃ i : Fin N, (N : ℝ) ^ (-(1 / 4 : ℝ)) <
            |cavityLam β (plantedMatrix β ω.1.1 ω.1.2) (plantedTilted β t ω.1.1 ω.1.2 ω.2) i|}
          ≤ ENNReal.ofReal (C * (N : ℝ) ^ (-a))) ∧
    (∀ (N : ℕ) (β t : ℝ) (W : Disorder N) (x : Spin N) (g : Fin N → ℝ) (i : Fin N),
      let M := plantedMatrix β W x
      let μ := plantedTilted β t W x g
      |(tapHessian β M μ * lawCov μ - 1) i i - cavityLam β M μ i * tapVar μ i| ≤ 2 * β ^ 2) := by sorry

end SKAnnealing.Sampling
