-- Prove2me | Theorems.Thm_SampQueryLB_WarmSLC_corollary_5_6
-- name    : SampQueryLB.WarmSLC.corollary_5_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:16:16.088436+00:00
-- url     : https://prove2.me/theorems/245f14d9-3dd1-4fb4-a961-3877a7c2ffb1
-- title:
--   Corollary 5.6 — decoupling of separated query groups: $\mathrm{TV}(P^{sh},P^{ind})\le\frac32\rho M$, $\rho=2\sqrt{st}\exp(-Kr^2/(4st))$
-- statement:
--   Consider the level-$i$ specialization of §3.3: a $q$-round measurement process of the coefficients, with seed in a standard Borel space (it may contain $\Xi_i,\dots,\Xi_h$), where each round $k$ selects, as Borel functions of the seed and the preceding measurements, a point $y_k$ (the current query or the output, for a terminal batch) and a label $\ell_k\in\{\mathrm{local},\mathrm{far}\}$, and its batch consists of vectors $\Phi_{j,p}(y_k)$ or $D_v\Phi_{j,p}(y_k)$ with $j<i$, together with zero vectors. In the shared model all batches measure $\Xi_{<i}$; in the independent model local and far batches measure independent copies.
--
--   **Corollary 5.6.** Let $s,t\ge1$ be integers with $K\ge2st$, let $r>0$ and $\rho=2\sqrt{st}\exp(-Kr^2/(4st))$. Suppose that for every seed value and every $z$, (i) at most $s$ rounds are labelled local and at most $t$ far, and (ii) for every local round $k$ and far round $\ell$ with $C_i(y_k)C_i(y_\ell)>0$, $\|\psi_i(y_k)-\psi_i(y_\ell)\|\ge r$ and $\|\psi_i(y_k)+\psi_i(y_\ell)\|\ge r$. If $\rho<1/2$ then
--   $$\mathrm{TV}(P^{sh},P^{ind})\le\tfrac32\rho M,$$
--   and the same bound holds for the laws of the algorithm's transcript and of its output.
--
--   **Formalization Note.** The process measures the whole coefficient vector $\Xi\in G_n$ with vectors supported on the levels $j<i$, which is the same as measuring $\Xi_{<i}$; the points $y_k$ are non-anticipating Borel maps `pt k`. The conclusion is stated for every measurable function of the full transcript.
--
--   Differences from the source:
--   - reading: the standing assumption of §4.1 that n is a sufficiently large integer → ∃ n0, ∀ n ≥ n0; reason: the construction is set up for large n only (§4.1); the statement itself has no constants C_f, C_g, η*, λ*
--   - encoding: x = (x_0, …, x_h) ∈ R^{d_n} with blocks x_j ∈ R^n; tensors in R^{n^{pS_i}} with ψ_i = u_i ⊗ u_{i+1}^{⊗K} ⊗ ⋯ → Point (dn n) with block j at coordinates finProdFinEquiv (j, a); G_n = EuclideanSpace on Σ (i,p), (Fin (p·S_i) → Fin n), slot r of ψ_i carrying block i + slotLevel K r; reason: a fixed labelling of coordinates and tensor slots; every statement is invariant under it
--   - encoding: Borel maps B_k(ω, Z_1, …, Z_{k−1}), L_k(ω, Z_1, …, Z_{k−1}) ∈ {local, far} → MeasProcess: measurable maps of (ω, whole record) that do not depend on rounds ≥ k; labels Bool (true = local); reason: non-anticipating maps of the whole record are exactly maps of the earlier rounds
--   - encoding: 'the same bound holds for the laws of the algorithm's transcript and of its output' → the bound for the image laws under every measurable function of the full transcript (f = id gives (4)/(42)); reason: the transcript and the output are Borel functions of the full transcript (§3.1); the quantified form contains both
--   - encoding: TV(·,·) = sup over measurable B of |ν(B) − ν'(B)| → TVAtMost μ ν ε (LogConcaveQuery): |μ.real B − ν.real B| ≤ ε for every measurable B; laws as Measure.map; reason: the same quantity, TV ≤ ε iff every measurable set is within ε
--   - encoding: batches measure Ξ_{<i} (resp. independent copies of it) → batches measure Ξ ∈ G_n (resp. independent copies) with vectors supported on the levels j < i; reason: ⟨Ξ, a⟩ = ⟨Ξ_{<i}, a⟩ for every such vector, so the transcripts have the same laws
--   - encoding: §5.3 fixes 1 ≤ i ≤ h → every level 0 ≤ i ≤ h; reason: at i = 0 there is no level j < i, so every measurement vector is zero and the statement holds trivially; no instance of the source changes
-- source:
--   Zhou, Suzuki, Towards the Query Complexity of Sampling under Strong Log-Concavity and Log-Sobolev Inequalities, arXiv:2611.05813 (held version dated November 3, 2026, sha256 966f8fc0…184c), p. 42, Corollary 5.6 (PDF p. 45)

import Mathlib
import Definitions.Def_LogConcaveQuery
import Definitions.Def_SampQueryLB_WarmSLC_Model
import Definitions.Def_SampQueryLB_WarmSLC_HardFamily
import Definitions.Def_SampQueryLB_WarmSLC_Measurement

open MeasureTheory OAI.LogConcaveSampling ProbabilityTheory

namespace SampQueryLB.WarmSLC

theorem corollary_5_6 :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ (i : Lvl n) (s t : ℕ), 1 ≤ s → 1 ≤ t → 2 * s * t ≤ KK n →
      ∀ r : ℝ, 0 < r →
      ∀ (O : Type) [MeasurableSpace O] [StandardBorelSpace O] (μO : Measure O)
        [IsProbabilityMeasure μO] (q : ℕ), 1 ≤ q → ∀ (m : Fin q → ℕ)
        (P : MeasProcess (Coef n) O q m) (pt : Fin q → O × Rec q m → Point (dn n)),
        (∀ k, Measurable (pt k)) →
        (∀ k w (z z' : Rec q m), (∀ j, j < k → z j = z' j) → pt k (w, z) = pt k (w, z')) →
        (∀ k w z b, P.batch k (w, z) b = 0 ∨
          ∃ (j : Lvl n) (p : Deg n), j < i ∧
            (P.batch k (w, z) b = feat j p (pt k (w, z)) ∨
              ∃ v : Point (dn n), P.batch k (w, z) b = fderiv ℝ (feat j p) (pt k (w, z)) v)) →
        (∀ w z, (Finset.univ.filter fun k => P.label k (w, z) = true).card ≤ s ∧
          (Finset.univ.filter fun k => P.label k (w, z) = false).card ≤ t) →
        (∀ w z k l, P.label k (w, z) = true → P.label l (w, z) = false →
          0 < Ccut i (pt k (w, z)) * Ccut i (pt l (w, z)) →
          r ≤ ‖psi i (pt k (w, z)) - psi i (pt l (w, z))‖ ∧
            r ≤ ‖psi i (pt k (w, z)) + psi i (pt l (w, z))‖) →
        2 * Real.sqrt ((s : ℝ) * t) * Real.exp (-((KK n : ℝ) * r ^ 2 / (4 * s * t))) < 1 / 2 →
        ∀ (β : Type) [MeasurableSpace β] (f : O × Rec q m → β), Measurable f →
          TVAtMost ((P.shLaw μO).map f) ((P.indLaw μO).map f)
            (3 / 2 * (2 * Real.sqrt ((s : ℝ) * t) * Real.exp (-((KK n : ℝ) * r ^ 2 / (4 * s * t)))) *
              ∑ k, (m k : ℝ)) := by sorry

end SampQueryLB.WarmSLC
