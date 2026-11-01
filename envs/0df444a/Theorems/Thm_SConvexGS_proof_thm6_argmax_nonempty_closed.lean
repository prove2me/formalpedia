-- Prove2me | Theorems.Thm_SConvexGS_proof_thm6_argmax_nonempty_closed
-- name    : SConvexGS.proof_thm6_argmax_nonempty_closed
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:50.146749+00:00
-- url     : https://prove2.me/theorems/151a803f-7b8a-40f7-949d-f68543c35d86
-- title:
--   Proof of Theorem 6, p.ec6 — a usc, coercive concave $f$ has $\operatorname{dom}(f_*)=\mathbb R^n$ and nonempty closed $\arg\max f[-q]$
-- statement:
--   Let $f:\mathbb R^n\to[-\infty,\infty)$ be upper semicontinuous, concave and coercive with $\operatorname{dom}(f)\ne\emptyset$. Then for every $q\in\mathbb R^n$:
--
--   1. $f_*(q)$ is finite, that is, $q\in\operatorname{dom}(f_*)$;
--   2. $\arg\max f[-q]$ is nonempty;
--   3. $\arg\max f[-q]$ is closed.
--
--   This is the first step of the proof of Theorem 6: it provides the point of $\arg\max f[-q]$ closest to a given $x$.
--
--   Differences from the source:
--   - encoding: f : ℝⁿ → [−∞, ∞) → f : (Fin n → ℝ) → EReal with ∀ x, f x ≠ ⊤; reason: Lean convention; same functions, with ⊥ for −∞
--   - encoding: f concave → ConcaveOn of toReal ∘ f on dom f (IsConcaveFn); reason: ConcaveOn needs a module target; with f < ∞ this is concavity of the extended-valued f
--   - encoding: arg max f[−p] → argMaxTilt f p, with no clause x ∈ dom f; reason: the same set when dom f ≠ ∅; at f ≡ −∞ every point maximizes, the reading under which Corollary 2 holds as printed
--   - encoding: lim_{‖x‖₂→+∞} f(x)/‖x‖₂ = −∞ → IsCoercive f: ∀ M, ∃ R, ‖x‖₂ ≥ R → f x ≤ M‖x‖₂; reason: equivalent to the limit, without a division in EReal
--   - generalization: f S-concave (the setting of Theorem 6) → f concave; reason: every S-concave function is concave, so this contains the paper's step
--   - encoding: the conjugate, defined on p.14 for dom f ≠ ∅ → hypothesis (dom f).Nonempty; reason: excludes f ≡ −∞ only, for which p.14 defines no conjugate
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Proof of Theorem 6, p.ec6

import Mathlib
import Definitions.Def_SConvexGS_IsConcaveFn
import Definitions.Def_SConvexGS_IsCoercive
import Definitions.Def_SConvexGS_concaveConj
import Definitions.Def_SConvexGS_argMaxTilt

namespace SConvexGS

/-- Proof of Theorem 6, p.ec6 (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29)):
for a usc, coercive concave `f` with nonempty domain, `dom(f₍*₎) = ℝⁿ`, and `arg max f[−q]` is
nonempty and closed for every `q`.

Formalization Note: the paper's `f` here is S-concave; only concavity is assumed. `(dom f).Nonempty`
excludes `f ≡ −∞`, for which p.14 does not define the conjugate. -/
theorem proof_thm6_argmax_nonempty_closed {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_top : ∀ x, f x ≠ ⊤) (hf_usc : UpperSemicontinuous f) (hf_concave : IsConcaveFn f)
    (hf_coercive : IsCoercive f) (hf_dom : (dom f).Nonempty) (q : Fin n → ℝ) :
    q ∈ dom (concaveConj f) ∧ (argMaxTilt f q).Nonempty ∧ IsClosed (argMaxTilt f q) := by sorry

end SConvexGS
