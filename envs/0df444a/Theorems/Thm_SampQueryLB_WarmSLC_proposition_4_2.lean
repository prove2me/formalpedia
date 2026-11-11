-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_proposition_4_2
-- name    : SampQueryLB.WarmSLC.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:16:57.882906+00:00
-- url     : https://prove2.me/theorems/e923e5a3-094a-4ba4-87db-31e45ed88b7b
-- title:
--   Proposition 4.2 — admissibility and parameter bounds: $\mu_n(E_n^c)\le2(h+1)Pe^{-n}$; $I\preceq\nabla^2V^\Xi_i\preceq2I$ on $E_n$; $\beta_h\ge n^{-1/16}$
-- statement:
--   Consider the hard family of §4.1 (definition `HardFamily`) with absolute constants $C_f,C_g,\eta_*,\lambda_*$.
--
--   **Proposition 4.2.** The absolute constants can be chosen so that, for all sufficiently large $n$:
--   1. $\mu_n(E_n^c)\le 2(h+1)Pe^{-n}$;
--   2. for every $\Xi\in E_n$, $0\le i\le h$ and $x\in\mathbb R^{d_n}$, $I_{d_n}\preceq\nabla^2V^\Xi_i(x)\preceq2I_{d_n}$; consequently $0$ is the unique minimizer of $V^\Xi_i$ and its target $\pi^\Xi_i$ has mean zero;
--   3. the amplitudes decrease and satisfy $\beta_h\ge n^{-1/16}$.
--
--   Moreover $\log S_0=O((\log n)^{2/3})$ and $\min_{i,p}a_{i,p}=n^{-o(1)}$:
--   $$\exists C\ \forall n\ge n_0:\ \log S_0\le C(\log n)^{2/3},\qquad \forall\varepsilon>0\ \exists n_1\ \forall n\ge n_1\ \forall i,p:\ a_{i,p}\ge n^{-\varepsilon}.$$
--
--   This is what makes the random potentials legitimate instances (condition number 2) and keeps the last amplitude polynomially large.
--
--   **Formalization Note.** The absolute constants $C_f, C_g, \eta_*, \lambda_*$ of the construction are quantified by `ForChosenConstants`: the statement holds for every $C_f\ge C_f^0$, then every $C_g\ge\max(1,C_g^0)$, then every $\eta_*\in(0,\min(1,\eta^0)]$, $\lambda_*\in(0,\min(1/2,\lambda^0)]$ with $\eta_*\lambda_*\le 1/4$ (the order and constraints of the proof of Proposition 4.2), and 'for all sufficiently large $n$' is $\exists n_0\,\forall n\ge n_0$. $V^\Xi_i$ is `Vpre c Ξ (i+1)`. The Hessian bound is the quadratic-form bound `HessianBetween _ 1 2`; "unique minimizer $0$" is $V(0)<V(x)$ for $x\ne0$; "mean zero" is integrability of $x$ under $\pi^\Xi_i$ with $\int x\,d\pi^\Xi_i=0$.
--
--   Differences from the source:
--   - reading: the absolute constants C_f, C_g, η*, λ* 'can be chosen' / are 'sufficiently large/small', n is 'a sufficiently large integer' (§4.1, proof of Proposition 4.2) → ForChosenConstants: the statement holds for all sufficiently extreme constants in the paper's choice order (C_f, then C_g ≥ 1, then η* ≤ 1, λ* ≤ 1/2, η*λ* ≤ 1/4), and for all n ≥ n0; reason: the paper fixes the constants once by monotone 'sufficiently' conditions; the for-all-sufficiently form implies the paper's existential choice and lets the thresholds of different results be combined
--   - encoding: x = (x_0, …, x_h) ∈ R^{d_n} with blocks x_j ∈ R^n; tensors in R^{n^{pS_i}} with ψ_i = u_i ⊗ u_{i+1}^{⊗K} ⊗ ⋯ → Point (dn n) with block j at coordinates finProdFinEquiv (j, a); G_n = EuclideanSpace on Σ (i,p), (Fin (p·S_i) → Fin n), slot r of ψ_i carrying block i + slotLevel K r; reason: a fixed labelling of coordinates and tensor slots; every statement is invariant under it
--   - reading: 'the amplitudes decrease' → β_{i+1} < β_i for i < h (strict); reason: (22) gives β_{i+1} = β_0β_i/(β_0 + D_i) with D_i ≥ 1, so the strict reading holds and is the stronger one
--   - encoding: log S_0 = O((log n)^{2/3}), min_{i,p} a_{i,p} = n^{−o(1)} → ∃ C > 0, ∃ n0, ∀ n ≥ n0, log S_0 ≤ C (log n)^{2/3}; ∀ ε > 0, eventually a_{i,p} ≥ n^{−ε} for all i, p; reason: the definitions of O and n^{−o(1)} (a_{i,p} ≤ 1 always)
--   - encoding: 0 is the unique minimizer; π^Ξ_i has mean zero → ∀ x ≠ 0, V(0) < V(x); MeanZero (Bochner-integrable identity with integral 0); reason: same meaning
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 27, Proposition 4.2 (PDF p. 30)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem proposition_4_2 :
    ForChosenConstants fun c =>
      (∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        (mu n (Eadm c n)ᶜ ≤
          ENNReal.ofReal (2 * ((hh n : ℝ) + 1) * PP n * Real.exp (-(n : ℝ)))) ∧
        (∀ Ξ ∈ Eadm c n, ∀ i : Lvl n,
          HessianBetween (Vpre c Ξ (i + 1)) 1 2 ∧
          (∀ x, x ≠ 0 → Vpre c Ξ (i + 1) 0 < Vpre c Ξ (i + 1) x) ∧
          MeanZero (gibbs (Vpre c Ξ (i + 1)))) ∧
        (∀ i : ℕ, i < hh n → beta c n (i + 1) < beta c n i) ∧
        (n : ℝ) ^ (-(1 / 16 : ℝ)) ≤ beta c n (hh n)) ∧
      (∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        Real.log (S n 0) ≤ C * Real.log n ^ ((2 : ℝ) / 3)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
        ∀ (i : Lvl n) (p : Deg n), (n : ℝ) ^ (-ε) ≤ aa n i p) := by sorry

end SampQueryLB.WarmSLC
