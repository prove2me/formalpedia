-- Prove2me | Theorems.Thm_TensorNP_Bilinear_lemma_2_10
-- name    : TensorNP.Bilinear.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:18.732207+00:00
-- url     : https://prove2.me/theorems/2536c657-ca55-4b85-ab35-0a538b468234
-- title:
--   Lemma 2.10 — $C_G$ has a nonzero complex zero iff $G$ is 3-colorable
-- statement:
--   Let $G$ be a simple graph on $v$ vertices and let $C_G$ be its color encoding (Definition 2.9), a set of $4v$ quadratic polynomials in the $2v+1$ unknowns $x_1,\dots,x_v,y_1,\dots,y_v,z$. Then
--   $$
--   \exists\, 0 \neq (x_1,\dots,x_v,y_1,\dots,y_v,z) \in \mathbb C^{2v+1} \text{ at which every polynomial of } C_G \text{ vanishes} \iff G \text{ is 3-colorable}.
--   $$
--
--   The lemma turns 3-colorability into the feasibility of a homogeneous quadratic system; the reduction of Theorem 3.7 is built on it.
--
--   **Formalization Note** 3-colorability is Mathlib's `SimpleGraph.Colorable 3`. For $v = 0$ both sides hold ($z = 1$ is a nonzero zero of the empty system).
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:14, Lemma 2.10 (proof p. 0:14–0:15)

import Mathlib
import Definitions.Def_TensorNP_Bilinear_ColorEncoding

namespace TensorNP.Bilinear

/-- Lemma 2.10 (p. 0:14): the color encoding `C_G` has a nonzero complex solution if and only if
`G` is 3-colorable. -/
theorem lemma_2_10 {v : ℕ} (G : SimpleGraph (Fin v)) :
    (∃ p : Fin (2 * v + 1) → ℂ, p ≠ 0 ∧ ∀ (c : Fin 4) (i : Fin v), colorEncoding G c i p = 0) ↔
      G.Colorable 3 := by sorry

end TensorNP.Bilinear
