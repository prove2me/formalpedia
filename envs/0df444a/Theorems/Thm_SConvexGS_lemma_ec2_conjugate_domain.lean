-- Prove2me | Theorems.Thm_SConvexGS_lemma_ec2_conjugate_domain
-- name    : SConvexGS.lemma_ec2_conjugate_domain
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:29:06.853578+00:00
-- url     : https://prove2.me/theorems/f468b176-dd06-47ca-9a01-247cdd6f6122
-- title:
--   Lemma EC.2 (corrected: $f$ concave; $f_*$ in (3)) — the interior of $\operatorname{dom}(f_*)$ is nonempty, upward closed and a sublattice
-- statement:
--   Let $f:\mathbb R^n\to[-\infty,\infty)$ be an upper semicontinuous concave proper GS-function with $\operatorname{dom}(f)\ne\emptyset$. Then:
--
--   1. $\operatorname{int}(\operatorname{dom}f_*)$ is nonempty;
--   2. if $p\in\operatorname{int}(\operatorname{dom}f_*)$, then $q\in\operatorname{int}(\operatorname{dom}f_*)$ for any $q\ge p$;
--   3. if $p\in\overline{\operatorname{dom}f_*}$, then $q\in\operatorname{int}(\operatorname{dom}f_*)$ for any $q$ with $q_i>p_i$ for all $i$;
--   4. for any $p,q\in\operatorname{int}(\operatorname{dom}f_*)$ (not necessarily ordered), the box $[p\wedge q,p\vee q]$ is contained in $\operatorname{int}(\operatorname{dom}f_*)$.
--
--   The lemma shows that the domain of the conjugate has the lattice structure needed for the supermodularity of $f_*$ in Theorem 7.
--
--   Differences from the source:
--   - encoding: f : ℝⁿ → [−∞, ∞) → f : (Fin n → ℝ) → EReal with ∀ x, f x ≠ ⊤; reason: Lean convention; same functions, with ⊥ for −∞
--   - encoding: f concave → ConcaveOn of toReal ∘ f on dom f (IsConcaveFn); reason: ConcaveOn needs a module target; with f < ∞ this is concavity of the extended-valued f
--   - encoding: arg max f[−p] → argMaxTilt f p, with no clause x ∈ dom f; reason: the same set when dom f ≠ ∅; at f ≡ −∞ every point maximizes, the reading under which Corollary 2 holds as printed
--   - correction: usc proper GS-function, with no concavity → adds IsConcaveFn f; reason: the printed statement is false: n = 2, S = {0} ∪ {(2k, k+1), (k+1, 2k) : k ≥ 1}, f = 0 at 0, −1 on the rest of S, −∞ off S, is usc and proper GS (proved in Solutions/verification/SConvexGS_Sanity4.lean); dom f₍*₎ = {p : 2p₁ + p₂ ≥ 0, p₁ + 2p₂ ≥ 0}, so a = (3, −1) and b = (−1, 3) lie in int(dom f₍*₎) while a ∧ b = (−1, −1) ∉ dom f₍*₎, and (4) fails
--   - correction: (3): p in the closure of dom f* (the convex conjugate) → p in the closure of dom f₍*₎ (the concave conjugate); reason: the printed statement is false: n = 1, f(x) = −x on [0, ∞), −∞ elsewhere, p = −5, q = −4 (proved in Solutions/verification/SConvexGS_Sanity3.lean); the paper's proof of (3) uses dom f₍*₎
--   - encoding: the conjugate, defined on p.14 for dom f ≠ ∅ → hypothesis (dom f).Nonempty; reason: excludes f ≡ −∞ only, for which p.14 defines no conjugate
--   - reading: q > p in (3) → ∀ i, p i < q i; reason: the paper does not define > on vectors; its proof of (3) takes q > pᵏ for pᵏ → p, which needs every coordinate strict, and the other reading (q ≥ p, q ≠ p) is false: f = 0 on {x ≤ 0}, −∞ elsewhere (n = 2) is usc, concave and proper GS with dom f₍*₎ = ℝ²₊, and p = 0, q = (1, 0) gives q ∉ int(dom f₍*₎)
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Lemma EC.2, p.ec7

import Mathlib
import Definitions.Def_SConvexGS_IsConcaveFn
import Definitions.Def_SConvexGS_IsProperGS
import Definitions.Def_SConvexGS_concaveConj

namespace SConvexGS

/-- **Lemma EC.2** (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29), p.ec7),
corrected: for a usc concave proper GS-function `f : ℝⁿ → [−∞, ∞)` with nonempty domain,
(1) `int(dom f₍*₎)` is nonempty;
(2) if `p ∈ int(dom f₍*₎)` then `q ∈ int(dom f₍*₎)` for any `q ≥ p`;
(3) if `p` is in the closure of `dom f₍*₎` then `q ∈ int(dom f₍*₎)` for any `q > p`;
(4) for any `p, q ∈ int(dom f₍*₎)` (not necessarily ordered), `[p ∧ q, p ∨ q] ⊆ int(dom f₍*₎)`.

Formalization Note: the printed lemma omits concavity and prints `dom f*` in (3); both printed forms
are false. `(dom f).Nonempty` excludes `f ≡ −∞`, for which p.14 does not define the conjugate. The
paper's `q > p` in (3) is strict in every coordinate, not Mathlib's `p < q` on `Fin n → ℝ`. -/
theorem lemma_ec2_conjugate_domain {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_top : ∀ x, f x ≠ ⊤) (hf_usc : UpperSemicontinuous f) (hf_concave : IsConcaveFn f)
    (hf_gs : IsProperGS f) (hf_dom : (dom f).Nonempty) :
    (interior (dom (concaveConj f))).Nonempty ∧
    (∀ p ∈ interior (dom (concaveConj f)), ∀ q, p ≤ q → q ∈ interior (dom (concaveConj f))) ∧
    (∀ p ∈ closure (dom (concaveConj f)), ∀ q : Fin n → ℝ, (∀ i, p i < q i) →
      q ∈ interior (dom (concaveConj f))) ∧
    (∀ p ∈ interior (dom (concaveConj f)), ∀ q ∈ interior (dom (concaveConj f)),
      Set.Icc (p ⊓ q) (p ⊔ q) ⊆ interior (dom (concaveConj f))) := by sorry

end SConvexGS
