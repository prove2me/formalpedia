-- Prove2me | Theorems.Thm_PseudoRiemannian_minkowski_pseudo_riemannian
-- name    : PseudoRiemannian.minkowski_pseudo_riemannian
-- status  : Open
-- author  : @LG
-- created : 2026-11-27T02:30:00.837948+00:00
-- url     : https://prove2.me/theorems/8f5b26fe-05d0-4672-a91e-cef5aca4dc74
-- title:
--   The model space: Minkowski R^{1,3} is pseudo-Riemannian of Lorentzian signature
-- statement:
--   **The model space — Minkowski $R^{1,3}$ is pseudo-Riemannian.**
--
--   "the model space for a pseudo-Riemannian manifold of signature (p, q) is pseudo-Euclidean space R^{p,q}"; "Minkowski space R^{n-1,1} with the flat Minkowski metric is the local model of a Lorentzian manifold"; "A principal premise of general relativity is that spacetime can be modeled as a 4-dimensional Lorentzian manifold of signature (3, 1) or, equivalently, (1, 3)."
--
--   **Conclusion:** the constant metric $x \mapsto \eta$ on `Spc 4` (with $\eta = \mathrm{diag}(-1, 1, 1, 1) = $ `etaM`) is pseudo-Riemannian with signature vector `minkDiag`:
--
--   $$\mathrm{IsPseudoRiemannian}\ (\mathrm{fun}\ x \mapsto \eta)\ \mathrm{minkDiag}.$$
--
--   Unfolding the definition, this is three things at once: symmetry ($\eta$ is diagonal), smoothness (the components are constant functions — $C^\infty$), and the signature witness with $B$ the identity matrix ($1^{T}\,\eta\,1 = \eta = \mathrm{diag}(\mathrm{minkDiag})$).
--
--   In words: the flat Lorentzian spacetime of relativity — the article's local model — satisfies the definition of a pseudo-Riemannian metric of Lorentzian signature.
--
--   **Formalization note.** The identity matrix is its own transpose, `Matrix.one_mul`, `Matrix.mul_one`, and `etaM = Matrix.diagonal minkDiag` by definition; smoothness of constant maps is `ContDiff.const`. The definition of `etaM` carries the diagonal structure directly, so symmetry is `Matrix.IsSymm`-style entrywise equality on a diagonal matrix.
-- source:
--   Wikipedia, Pseudo-Riemannian manifold, https://en.wikipedia.org/wiki/Pseudo-Riemannian_manifold (source of the quoted statements, reproduced verbatim in the definition file) ('Minkowski space R^{n-1,1} with the flat Minkowski metric is the local model of a Lorentzian manifold'; 'A principal premise of general relativity is that spacetime can be modeled as a 4-dimensional Lorentzian manifold of signature (3, 1) or, equivalently, (1, 3)'); H. Minkowski, Raum und Zeit (1908)

import Mathlib
import Definitions.Def_PseudoRiemannian

namespace PseudoRiemannian

open Matrix
open scoped ContDiff

/-- Milestone: the model space.  "Minkowski space R^{n-1,1} with the flat
Minkowski metric is the local model of a Lorentzian manifold"; "A principal
premise of general relativity is that spacetime can be modeled as a
4-dimensional Lorentzian manifold of signature (3, 1) or, equivalently, (1, 3)."
The constant metric `x ↦ etaM` on `Spc 4` — signature diagonal `(-1, 1, 1, 1)`
— is a pseudo-Riemannian metric with signature vector `minkDiag`: symmetric
(diagonal), smooth (constant components), and witnessed by the identity
congruence. -/
theorem minkowski_pseudo_riemannian :
    IsPseudoRiemannian (fun _ : Spc 4 => etaM) minkDiag := by
  sorry

end PseudoRiemannian
