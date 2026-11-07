-- Prove2me | Theorems.Thm_PlantedIQP_lemma_16
-- name    : PlantedIQP.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:27.1625+00:00
-- url     : https://prove2.me/theorems/001f00b7-1e8b-4a56-b292-efa25fdb8381
-- title:
--   Lemma 16 — the polarization identity $T_f(u,v,w)=\sum f(\cdot)$
-- statement:
--   Let $f$ be a cubic polynomial with constant term $0$ and $T_f$ its alternating trilinear form. Then for all $u,v,w\in\mathbb F_2^n$,
--
--   $$
--   T_f(u,v,w)=f(u+v+w)+f(u+v)+f(v+w)+f(u+w)+f(u)+f(v)+f(w).
--   $$
--
--   The identity expresses $T_f$ through evaluations of $f$; it underlies the transformation rules of Proposition 18.
--
--   Differences from the source: none.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Lemma 16, Eq. (14), p.14

import Mathlib
import Definitions.Def_PlantedIQP_triForm

set_option autoImplicit false

namespace PlantedIQP

/-- Bläser, Gullans, Hangleiter, Liu, Qiao, *Verifiable quantum advantage based on polynomials with
planted structures*, arXiv:2609.39918 (sha256 6e261694…), Lemma 16, p.14, Eq. (14): for a cubic polynomial `f` (constant term
`0`) and its alternating trilinear form `T_f` (Definition 15), for all `u, v, w ∈ 𝔽₂ⁿ`,
`T_f(u, v, w) = f(u+v+w) + f(u+v) + f(v+w) + f(u+w) + f(u) + f(v) + f(w)`. -/
theorem lemma_16 {n : ℕ} (f : CubicPoly n) (u v w : Vec n) :
    triForm f u v w = f.eval (u + v + w) + f.eval (u + v) + f.eval (v + w) + f.eval (u + w) +
      f.eval u + f.eval v + f.eval w := by sorry

end PlantedIQP
