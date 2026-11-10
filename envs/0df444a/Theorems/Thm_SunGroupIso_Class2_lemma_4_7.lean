-- Prove2me | Theorems.Thm_SunGroupIso_Class2_lemma_4_7
-- name    : SunGroupIso.Class2.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:06:07.30458+00:00
-- url     : https://prove2.me/theorems/207e32d9-e0de-4ffa-b1dc-9c4e8593c293
-- title:
--   Lemma 4.7 — G = ⟨H, g_1, …, g_k⟩ splits as at most bk cyclic factors plus a subgroup of H
-- statement:
--   Let $G$ be a finite abelian $p$-group of exponent $p^b$, $H\le G$, and $G=\langle H,g_1,\dots,g_k\rangle$. Then there are $m\le bk$ elements $x_1,\dots,x_m\in G$ and a subgroup $K\le H$ with $G=\langle x_1\rangle\oplus\cdots\oplus\langle x_m\rangle\oplus K$.
--
--   Differences from the source: none.
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 4.7, p. 17 (PDF p. 19)

import Mathlib
import Definitions.Def_SunGroupIso_Class2_Basic

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Lemma 4.7** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 4.7, p. 17, PDF p. 19). Let `G` be a finite abelian `p`-group of exponent
`p^b`, `H ≤ G`, and `G = ⟨H, g_1, …, g_k⟩`. Then there are `m ≤ bk` elements `x_1, …, x_m ∈ G` and a subgroup
`K ≤ H` with `G = ⟨x_1⟩ ⊕ ⋯ ⊕ ⟨x_m⟩ ⊕ K`. -/
theorem lemma_4_7 {p : ℕ} (hp : p.Prime) {G : Type*} [CommGroup G] [Finite G] (hG : IsPGroup p G)
    (b : ℕ) (hb : Monoid.exponent G = p ^ b) (H : Subgroup G) (k : ℕ) (g : Fin k → G)
    (hgen : Subgroup.closure ((H : Set G) ∪ Set.range g) = ⊤) :
    ∃ m ≤ b * k, ∃ x : Fin m → G, ∃ K : Subgroup G, K ≤ H ∧ DecompWith ⊤ x K := by sorry

end SunGroupIso.Class2
