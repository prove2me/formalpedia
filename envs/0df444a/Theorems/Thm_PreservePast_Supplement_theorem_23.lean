-- Prove2me | Theorems.Thm_PreservePast_Supplement_theorem_23
-- name    : PreservePast.Supplement.theorem_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T04:45:00.305834+00:00
-- url     : https://prove2.me/theorems/f31be70f-bf98-4ca7-a3d8-6906c9b8bb8b
-- title:
--   Theorem 23 — same-error LP law up to a logarithmic additive term
-- statement:
--   Fix $0<\beta<1$, $0<\theta<1$, and integers $K,D\ge1$. For every nonempty finite cap class $\mathcal V\subseteq(S^{D-1})^K$,
--   $$\log_2P_\beta(\mathcal V)\le B_\beta(\mathcal V,\theta)\le\log_2P_\beta(\mathcal V)+\log_2(1+KD)+C_{\beta,\theta},$$
--   where $C_{\beta,\theta}$ is independent of $K,D,\mathcal V$. For compact classes the same holds with $P^\ast_\beta$. As $KD\to\infty$,
--   $$\frac{B_\beta-\log_2P^\ast_\beta}{KD}\to0 .$$
--   Thus $B_\beta=\Theta(KD)$ exactly when $\log_2P^\ast_\beta=\Theta(KD)$, and $B_\beta=o(KD)$ exactly when $\log_2P^\ast_\beta=o(KD)$. If $\log(1+KD)=o(K)$, including fixed $D$ and $K\to\infty$, the same equivalences hold with $K$ in place of $KD$. For finite classes the star may be omitted.
--
--   The one-way LP therefore characterizes the memory of correlated response classes at the same error, up to a logarithmic additive term.
--
--   Differences from the source:
--   - encoding: (274) for finite classes with P_β and for compact classes with P*_β; for finite classes the star may be omitted → the bounds for every nonempty compact class with P*_β, and P*_β(F) = P_β(F) for a finite class F; reason: a finite class is compact, so the two statements together are the source's
--   - encoding: bounds on the least width B_β → a lower bound for every achieving width and an achieving protocol for the upper bound; reason: two-part form of a least width
--   - encoding: (B_β − log₂P*_β)/(KD) → 0 as KD → ∞ → for every η > 0 a threshold N such that KD ≥ N gives an achieving width ≤ log₂P*_β + ηKD, for every class; reason: the limit is uniform over classes; the lower side is the first inequality
--   - encoding: B_β = Θ(KD) exactly when log₂P*_β = Θ(KD), and likewise for o and for K → the equivalences for every sequence (K_n, D_n, 𝒱_n) of nonempty compact classes with K_nD_n → ∞, in Mathlib's =Θ and =o along n → ∞; reason: the asymptotic statements are about sequences of classes
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), Theorem 23, p.73 (PDF p.75), eq. (274)

import Mathlib
import Definitions.Def_PreservePast_Supplement_CapAchieves

open MeasureTheory Filter Asymptotics

namespace PreservePast.Supplement

/-- **Theorem 23 (Same-error LP law up to a logarithmic additive term).** P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), Theorem 23, p.73
(PDF p.75), eq. (274).

Fix `0 < β < 1`, `0 < θ < 1`. There is `C_{β,θ}`, independent of `K, D, 𝒱`, such that for all
`K, D ≥ 1` and every nonempty compact cap class `𝒱 ⊆ (S^{D−1})^K`:
`log₂ P*_β(𝒱) ≤ B_β(𝒱, θ) ≤ log₂ P*_β(𝒱) + log₂(1 + KD) + C_{β,θ}`, and for a finite class
`P*_β = P_β` (so (274) holds with `P_β`). As `KD → ∞`, `(B_β − log₂ P*_β)/(KD) → 0`;
`B_β = Θ(KD)` exactly when `log₂ P*_β = Θ(KD)`, `B_β = o(KD)` exactly when
`log₂ P*_β = o(KD)`, and if `log(1 + KD) = o(K)` the same equivalences hold with `K` in place of
`KD`.

**Formalization Note.** A finite class is compact, so (274) for finite classes is the compact
statement together with the clause `P*_β(F) = P_β(F)` ("For finite classes the star may be
omitted"). The bounds on `B_β` are in the two-part form (every achieving width; an achieving
protocol), with coin spaces in `Type`. The limit `(B_β − log₂ P*_β)/(KD) → 0` is uniform over the
classes: for every `η > 0` there is `N` such that `KD ≥ N` gives an achieving width
`≤ log₂ P*_β + η KD` (the lower side is the first inequality). The `Θ` and `o` equivalences are
stated for arbitrary sequences `(K_n, D_n, 𝒱_n)` of nonempty compact classes with
`K_n D_n → ∞`, using `capWidth` (the least width, which exists by the upper bound). -/
theorem theorem_23 :
    ∀ β θ : ℝ, 0 < β → β < 1 → 0 < θ → θ < 1 →
      (∃ C : ℝ, ∀ (K D : ℕ) (𝒱 : Set (Fin K → EuclideanSpace ℝ (Fin D))),
        1 ≤ K → 1 ≤ D → 𝒱 ⊆ capSpace K D → 𝒱.Nonempty → IsCompact 𝒱 →
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
            (enc : (Fin K → EuclideanSpace ℝ (Fin D)) → Ω → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → Ω → Fin K → EuclideanSpace ℝ (Fin D)),
            CapAchieves 𝒱 θ β P enc dec → Real.logb 2 (capLPStar 𝒱 θ β) ≤ (B : ℝ)) ∧
        (∃ B : ℕ, (B : ℝ) ≤ Real.logb 2 (capLPStar 𝒱 θ β) + Real.logb 2 (1 + K * D) + C ∧
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
            (enc : (Fin K → EuclideanSpace ℝ (Fin D)) → Ω → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → Ω → Fin K → EuclideanSpace ℝ (Fin D)),
            CapAchieves 𝒱 θ β P enc dec) ∧
        ∀ F : Finset (Fin K → EuclideanSpace ℝ (Fin D)), (F : Set _) = 𝒱 →
          capLPStar 𝒱 θ β = capLP F θ β) ∧
      (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ (K D : ℕ) (𝒱 : Set (Fin K → EuclideanSpace ℝ (Fin D))),
        1 ≤ K → 1 ≤ D → N ≤ K * D → 𝒱 ⊆ capSpace K D → 𝒱.Nonempty → IsCompact 𝒱 →
        ∃ B : ℕ, (B : ℝ) ≤ Real.logb 2 (capLPStar 𝒱 θ β) + η * (K * D) ∧
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
            (enc : (Fin K → EuclideanSpace ℝ (Fin D)) → Ω → Fin (2 ^ B))
            (dec : Fin (2 ^ B) → Ω → Fin K → EuclideanSpace ℝ (Fin D)),
            CapAchieves 𝒱 θ β P enc dec) ∧
      ∀ (K D : ℕ → ℕ) (𝒱 : ∀ n, Set (Fin (K n) → EuclideanSpace ℝ (Fin (D n)))),
        (∀ n, 1 ≤ K n ∧ 1 ≤ D n ∧ 𝒱 n ⊆ capSpace (K n) (D n) ∧ (𝒱 n).Nonempty ∧
          IsCompact (𝒱 n)) →
        Tendsto (fun n => K n * D n) atTop atTop →
        (((fun n => (capWidth (𝒱 n) θ β : ℝ)) =Θ[atTop] (fun n => ((K n * D n : ℕ) : ℝ)) ↔
            (fun n => Real.logb 2 (capLPStar (𝒱 n) θ β)) =Θ[atTop]
              (fun n => ((K n * D n : ℕ) : ℝ))) ∧
          ((fun n => (capWidth (𝒱 n) θ β : ℝ)) =o[atTop] (fun n => ((K n * D n : ℕ) : ℝ)) ↔
            (fun n => Real.logb 2 (capLPStar (𝒱 n) θ β)) =o[atTop]
              (fun n => ((K n * D n : ℕ) : ℝ))) ∧
          ((fun n => Real.log (1 + (K n * D n : ℕ))) =o[atTop] (fun n => (K n : ℝ)) →
            ((fun n => (capWidth (𝒱 n) θ β : ℝ)) =Θ[atTop] (fun n => (K n : ℝ)) ↔
              (fun n => Real.logb 2 (capLPStar (𝒱 n) θ β)) =Θ[atTop] (fun n => (K n : ℝ))) ∧
            ((fun n => (capWidth (𝒱 n) θ β : ℝ)) =o[atTop] (fun n => (K n : ℝ)) ↔
              (fun n => Real.logb 2 (capLPStar (𝒱 n) θ β)) =o[atTop]
                (fun n => (K n : ℝ))))) := by sorry

end PreservePast.Supplement
