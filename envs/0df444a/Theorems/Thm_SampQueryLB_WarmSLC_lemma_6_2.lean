-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_lemma_6_2
-- name    : SampQueryLB.WarmSLC.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:17:11.852996+00:00
-- url     : https://prove2.me/theorems/b8c29014-a19c-4622-9d23-5806ea6baed4
-- title:
--   Lemma 6.2 — first-moment bounds: $\mathbb EZ\le M$, $\mathbb EZ_{good}\ge(1-\eta_n)M$, $\mathbb EZ_{bad}\le\eta_nM$, $\eta_n\le e^{-n^{3/4}}$
-- statement:
--   With the masses of §6.1 (definition `Experiments`) under the unconditioned coefficient law $\mu_n$:
--
--   **Lemma 6.2.** For all sufficiently large $n$,
--   $$\mathbb E_{\Xi\sim\mu_n}Z\le M,\qquad \mathbb E_{\Xi\sim\mu_n}Z_{\mathrm{good}}\ge(1-\eta_n)M,\qquad \mathbb E_{\Xi\sim\mu_n}Z_{\mathrm{bad}}\le\eta_nM,$$
--   where $0\le\eta_n\le e^{-n^{3/4}}$.
--
--   **Formalization Note.** The absolute constants $C_f, C_g, \eta_*, \lambda_*$ of the construction are quantified by `ForChosenConstants`: the statement holds for every $C_f\ge C_f^0$, then every $C_g\ge\max(1,C_g^0)$, then every $\eta_*\in(0,\min(1,\eta^0)]$, $\lambda_*\in(0,\min(1/2,\lambda^0)]$ with $\eta_*\lambda_*\le 1/4$ (the order and constraints of the proof of Proposition 4.2), and 'for all sufficiently large $n$' is $\exists n_0\,\forall n\ge n_0$. For each such $n$ the Lean statement asserts a number $\eta_n\in[0,e^{-n^{3/4}}]$ with the three bounds.
--
--   Differences from the source:
--   - reading: the absolute constants C_f, C_g, η*, λ* 'can be chosen' / are 'sufficiently large/small', n is 'a sufficiently large integer' (§4.1, proof of Proposition 4.2) → ForChosenConstants: the statement holds for all sufficiently extreme constants in the paper's choice order (C_f, then C_g ≥ 1, then η* ≤ 1, λ* ≤ 1/2, η*λ* ≤ 1/4), and for all n ≥ n0; reason: the paper fixes the constants once by monotone 'sufficiently' conditions; the for-all-sufficiently form implies the paper's existential choice and lets the thresholds of different results be combined
--   - encoding: x = (x_0, …, x_h) ∈ R^{d_n} with blocks x_j ∈ R^n; tensors in R^{n^{pS_i}} with ψ_i = u_i ⊗ u_{i+1}^{⊗K} ⊗ ⋯ → Point (dn n) with block j at coordinates finProdFinEquiv (j, a); G_n = EuclideanSpace on Σ (i,p), (Fin (p·S_i) → Fin n), slot r of ψ_i carrying block i + slotLevel K r; reason: a fixed labelling of coordinates and tensor slots; every statement is invariant under it
--   - encoding: real-valued masses Z, Z_good, Z_bad, M and m(x) = E exp[−Σ β_i H_i(x)] → lower Lebesgue integrals in [0, ∞]; m(x) as its defining expectation; reason: all integrands are nonnegative; the values are finite and agree with the real ones
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 50, Lemma 6.2 (PDF p. 53)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Experiments

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory Filter
open scoped ENNReal ContDiff RealInnerProductSpace Topology

namespace SampQueryLB.WarmSLC

theorem lemma_6_2 :
    ForChosenConstants fun c => ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
      ∃ η : ℝ, 0 ≤ η ∧ η ≤ Real.exp (-((n : ℝ) ^ ((3 : ℝ) / 4))) ∧
        ∫⁻ Ξ, Zmass c Ξ ∂mu n ≤ Mmass c n ∧
        ENNReal.ofReal (1 - η) * Mmass c n ≤ ∫⁻ Ξ, Zgood c Ξ ∂mu n ∧
        ∫⁻ Ξ, Zbad c Ξ ∂mu n ≤ ENNReal.ofReal η * Mmass c n := by sorry

end SampQueryLB.WarmSLC
