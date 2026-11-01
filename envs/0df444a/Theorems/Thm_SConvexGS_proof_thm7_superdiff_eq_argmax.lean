-- Prove2me | Theorems.Thm_SConvexGS_proof_thm7_superdiff_eq_argmax
-- name    : SConvexGS.proof_thm7_superdiff_eq_argmax
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:27:55.277957+00:00
-- url     : https://prove2.me/theorems/b7eeccac-e839-482d-aa37-73202107a149
-- title:
--   Proof of Theorem 7, p.22 (corrected: $f$ concave) — $\partial f_*(p)=\arg\max f[-p]$
-- statement:
--   Let $f:\mathbb R^n\to[-\infty,\infty)$ be upper semicontinuous and concave (corrected: the printed step omits concavity) with $\operatorname{dom}(f)\ne\emptyset$. Then for every $p\in\mathbb R^n$,
--
--   $$\partial f_*(p)=\arg\max f[-p].$$
--
--   This is the conjugate duality through which the GS property of $f$ becomes a statement about the supergradients of $f_*$.
--
--   Differences from the source:
--   - encoding: f : ℝⁿ → [−∞, ∞) → f : (Fin n → ℝ) → EReal with ∀ x, f x ≠ ⊤; reason: Lean convention; same functions, with ⊥ for −∞
--   - encoding: f concave → ConcaveOn of toReal ∘ f on dom f (IsConcaveFn); reason: ConcaveOn needs a module target; with f < ∞ this is concavity of the extended-valued f
--   - correction: f a usc proper GS-function (the setting of Theorem 7), with no concavity → adds IsConcaveFn f; reason: the printed step is false without it: n = 1, f = 0 on {0, 2}, −∞ elsewhere, is usc and proper GS, f₍*₎(p) = min(0, 2p), and ∂f₍*₎(0) = [0, 2] ≠ {0, 2} = arg max f[−0]; Theorem 23.5 of Rockafellar (1970) needs a closed concave f, and Theorem 7 carries the same correction
--   - generalization: f a usc proper GS-function (the setting of Theorem 7) → no GS hypothesis; reason: the step uses only usc, concavity and dom f ≠ ∅; every function of the paper's setting satisfies these
--   - encoding: arg max f[−p] → argMaxTilt f p, with no clause x ∈ dom f; reason: the same set when dom f ≠ ∅; at f ≡ −∞ every point maximizes, the reading under which Corollary 2 holds as printed
--   - encoding: the conjugate, defined on p.14 for dom f ≠ ∅ → hypothesis (dom f).Nonempty; reason: excludes f ≡ −∞ only, for which p.14 defines no conjugate
--   - generalization: p ∈ [a ∧ b, a ∨ b], a box inside int(dom f₍*₎) → every p; reason: this contains the paper's case; off dom f₍*₎ both sides are empty
-- source:
--   Chen, Li, S-Convexity and Gross Substitutability, SSRN 3549632 (PDF of 2021-10-29), Proof of Theorem 7, p.22

import Mathlib
import Definitions.Def_SConvexGS_IsConcaveFn
import Definitions.Def_SConvexGS_concaveConj
import Definitions.Def_SConvexGS_superdiff
import Definitions.Def_SConvexGS_argMaxTilt

namespace SConvexGS

/-- Proof of Theorem 7, p.22 (Chen, Li, *S-Convexity and Gross Substitutability*, SSRN 3549632 (PDF of 2021-10-29)):
corrected: for a usc concave `f : ℝⁿ → [−∞, ∞)` with nonempty domain, `∂f₍*₎(p) = arg max f[−p]`.

Formalization Note: the printed step sits in the proof of Theorem 7, whose `f` is only a usc proper
GS-function; without concavity it is false (`f = 0` on `{0, 2} ⊂ ℝ`, `−∞` elsewhere, gives
`∂f₍*₎(0) = [0, 2] ≠ {0, 2}`), and Theorem 7 carries the same correction. The GS hypothesis is not
used and is dropped. The paper uses this for `p` in a box inside `int(dom f₍*₎)`; it is stated for
every `p`. Both sides are empty at `p ∉ dom f₍*₎`. `(dom f).Nonempty` excludes `f ≡ −∞`, for which
p.14 does not define the conjugate. -/
theorem proof_thm7_superdiff_eq_argmax {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_top : ∀ x, f x ≠ ⊤) (hf_usc : UpperSemicontinuous f) (hf_concave : IsConcaveFn f)
    (hf_dom : (dom f).Nonempty) (p : Fin n → ℝ) :
    superdiff (concaveConj f) p = argMaxTilt f p := by sorry

end SConvexGS
