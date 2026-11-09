-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_lemma_3_2
-- name    : ResPCDegreeSize.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:22:33.789548+00:00
-- url     : https://prove2.me/theorems/28ef7bb5-fe54-4348-b5a7-6101014d7c4a
-- title:
--   Lemma 3.2 — Frobenius descent of subspaces
-- statement:
--   Let $E$ be a field of characteristic $p$ and $W\subseteq E^m$ an $E$-linear subspace. For $u=(u_1,\dots,u_m)$ write $u^{[p]}=(u_1^p,\dots,u_m^p)$. If $u^{[p]}\in W$ for every $u\in W$, then
--   $$W=E\otimes_{\mathbb F_p}(W\cap\mathbb F_p^m)$$
--   under the natural identification inside $E^m$; that is, $W$ is spanned over $E$ by its vectors with all coordinates in $\mathbb F_p$.
--
--   So a subspace stable under coordinatewise Frobenius is defined over the prime field.
--
--   Differences from the source:
--   - encoding: a field E of characteristic p → a field E with an Algebra (ZMod p) E instance; reason: a field has such an instance exactly when its characteristic is p, and then the instance is unique
--   - encoding: E ⊗ (W ∩ F_p^m) inside E^m → the E-span of the vectors of W with all coordinates in the image of F_p; reason: this is the natural identification named in the source
--   - encoding: E^m and F_p → Fin m → E and ZMod p with [Fact p.Prime]; reason: relabelling of coordinates; ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Lemma 3.2, PDF p. 5 (printed p. 4)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem lemma_3_2 {p m : ℕ} [Fact p.Prime] {E : Type*} [Field E] [Algebra (ZMod p) E]
    (W : Submodule E (Fin m → E))
    (hW : ∀ u ∈ W, (fun j => u j ^ p) ∈ W) :
    W = Submodule.span E
      {v : Fin m → E | v ∈ W ∧ ∀ j, v j ∈ Set.range (algebraMap (ZMod p) E)} := by sorry

end ResPCDegreeSize.Main
