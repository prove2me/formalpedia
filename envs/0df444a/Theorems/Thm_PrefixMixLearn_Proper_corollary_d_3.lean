-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_corollary_d_3
-- name    : PrefixMixLearn.Proper.corollary_d_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:47:45.091933+00:00
-- url     : https://prove2.me/theorems/0617140b-0b67-4735-93b0-b47295c279ff
-- title:
--   Corollary D.3 — individual-profile list from R = ⌈(2/λ_min) log(2/δ)⌉ paths contains a mixture within 2^12η/(gu)
-- statement:
--   In the two-view setting of Theorem D.2 (without the assumptions on $r$), put $\lambda_{\min}=\min(w,1-w)$, $\lambda_0=1-w$, $\lambda_1=w$, $Q_0=Q_\nu$, $Q_1=Q_\mu$, and assume $\eta\le\lambda_{\min}g/1024$. For $0<\delta<1$ draw $R=\lceil(2/\lambda_{\min})\log(2/\delta)\rceil$ independent paths from $P_A$; on each path and for each $j$ take the clipped component profile $\hat\mu^{(j)}$ of $N_j$ (uniform mean vector if a parent mass is nonpositive), and form all $R^2$ pairs with common weight $w'$. Every entry of this list is a proper balanced mixture in $\mathcal M_{2,\alpha,d}$, and with probability at least $1-\delta$ the list contains $\hat M_A$ with
--   $$d_{TV}(P_A,\hat M_A)\le\frac{2^{12}}{gu}\eta.$$
--   Moreover, for each component $j$ there is a path event of $P_A$-probability at least $\lambda_j/2$ on which $d_{TV}(Q_{\hat\mu^{(j)}},Q_j)\le512\eta/(\lambda_jg\sqrt{\alpha u})$ and every parent prefix $h$ satisfies $N_j[h]/P_A[h]\ge\lambda_j/64$. This is the strong-signal (large test gap) branch of the learner.
--
--   Differences from the source:
--   - generalization: B a finite future view; laws R_0, R_1 on it → any finite type Y with laws R0 R1 : Y → ℝ; reason: the proof uses only that the future view is a finite set carrying the laws R_0, R_1, P_AB and the test e; a future view B of the cube is the finite set {0,1}^B, so the statement specializes to the source
--   - encoding: R independent paths from P_A; the list of R² pairs → iidProb (marginal P_A) R of the event ∃ k l, tv P_A (mixLaw w′ (profile N_0 on path k) (profile N_1 on path l)) ≤ …; reason: the list contains such an M̂_A exactly when some pair of path indices gives it
--   - encoding: the scalars a, b, η named in the setting → real variables with defining hypotheses; reason: same values
--   - encoding: coordinates i = 1, …, T; laws on {0,1}^T → `Fin T`, coordinate i ↦ i.val + 1; laws are real functions on `Fin T → Bool` with `IsLaw`; reason: Lean convention; same statement
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 34–35 (PDF 36–37), Corollary D.3, (D.11)–(D.13)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws
import Definitions.Def_PrefixMixLearn_Proper_Geometry
import Definitions.Def_PrefixMixLearn_Proper_Unmixing

namespace PrefixMixLearn.Proper

/-- Corollary D.3 (individual reconstruction using a supplied test). In the setting of §D.2 without
the weak-separation assumptions on `r`, with `λ_min = min(w, 1 − w)` and `η ≤ λ_min g/1024`
(D.11): from `R = ⌈(2/λ_min) log(2/δ)⌉` independent paths of `P_A`, the `R²` pairs of clipped
component profiles with common weight `w′` form a list of proper balanced mixtures (every pair of
paths gives an element of `M_{2,α,d}`) which contains, with probability at least `1 − δ`, a mixture
within `(2^{12}/(gu)) η` of `P_A` (D.12); and for each component `j` there is a path event of
`P_A`-probability at least `λ_j/2` on which `d_TV(Q_{μ̂^{(j)}}, Q_j) ≤ 512η/(λ_j g √(αu))` and every
parent prefix has `N_j[h]/P_A[h] ≥ λ_j/64` (D.13). -/
theorem corollary_d_3 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 / 2) (d : ℕ) (hd : 1 ≤ d)
    {Y : Type*} [Fintype Y]
    (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1) (ν μ : Fin d → ℝ) (hν : InBox α ν) (hμ : InBox α μ)
    (R0 R1 : Y → ℝ) (hR0 : IsLaw R0) (hR1 : IsLaw R1)
    (PAB : Cube d × Y → ℝ) (hP : IsLaw PAB) (hPf : FullSupport PAB)
    (e : Y → ℝ) (he : ∀ y, 0 ≤ e y ∧ e y ≤ 1)
    (a b : ℝ) (ha : a = testMean R0 e) (hb : b = testMean R1 e) (hg : 0 < b - a)
    (η : ℝ) (hηdef : η = tv PAB (condProdMix w ν μ R0 R1))
    (hη : η ≤ min w (1 - w) * (b - a) / 1024)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ x x' : Cube d, mixLaw (wPrime PAB e a b) (indivProfile α (unmixN0 PAB e a b) x)
        (indivProfile α (unmixN1 PAB e a b) x') ∈ M2Class α d) ∧
    1 - δ ≤ iidProb (marginalA PAB) ⌈2 / min w (1 - w) * Real.log (2 / δ)⌉₊
        (fun xs => ∃ k l, tv (marginalA PAB)
          (mixLaw (wPrime PAB e a b) (indivProfile α (unmixN0 PAB e a b) (xs k))
            (indivProfile α (unmixN1 PAB e a b) (xs l))) ≤ (2 : ℝ) ^ 12 / ((b - a) * uOf α) * η) ∧
    (∃ G : Set (Cube d), (1 - w) / 2 ≤ massOf (marginalA PAB) G ∧
      ∀ x ∈ G,
        tv (prodLaw (indivProfile α (unmixN0 PAB e a b) x)) (prodLaw ν) ≤
            512 * η / ((1 - w) * (b - a) * Real.sqrt (α * uOf α)) ∧
        ∀ t : ℕ, t < d →
          (1 - w) / 64 ≤ prefMass (unmixN0 PAB e a b) x t / prefMass (marginalA PAB) x t) ∧
    (∃ G : Set (Cube d), w / 2 ≤ massOf (marginalA PAB) G ∧
      ∀ x ∈ G,
        tv (prodLaw (indivProfile α (unmixN1 PAB e a b) x)) (prodLaw μ) ≤
            512 * η / (w * (b - a) * Real.sqrt (α * uOf α)) ∧
        ∀ t : ℕ, t < d →
          w / 64 ≤ prefMass (unmixN1 PAB e a b) x t / prefMass (marginalA PAB) x t) := by sorry

end PrefixMixLearn.Proper
