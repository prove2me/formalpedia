-- Prove2me | Theorems.Thm_StableSKC_Galois_scale_round_formula
-- name    : StableSKC.Galois.scale_round_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:22.138269+00:00
-- url     : https://prove2.me/theorems/c189e188-3722-431b-b157-f47b1b4d094e
-- title:
--   §3.3, p. 11 — v_{T(z)}(x, y) = v_{T(z)}(0, x − y) and v_{T(z)}(0, y) = 1 + d(z^{−1}y)
-- statement:
--   Let $\mathrm{GF}(2^k)$ be presented with a root $\alpha$ of an irreducible polynomial of degree $k$ over $\mathbb Z_2$, with degree function $d$, and let $T$ be a knockout tournament on the elements of $\mathrm{GF}(2^k)$ satisfying Lemma 3.1, i.e. $v_T(x, y) = 1 + d(x - y)$ for all distinct $x, y$. Let $z \in \mathrm{GF}(2^k)$ be nonzero and let $T(z)$ be obtained from $T$ by replacing each player $x$ with $zx$. Then:
--
--   1. for all distinct $x, y \in \mathrm{GF}(2^k)$,
--   $$v_{T(z)}(x, y) = v_{T(z)}(0, x - y);$$
--   2. for all nonzero $y \in \mathrm{GF}(2^k)$,
--   $$v_{T(z)}(0, y) = 1 + d(z^{-1} y).$$
--
--   So in every relabelled tournament the meeting round of two players depends only on their difference, and is computed explicitly by the degree. Theorem 3.1 follows from these identities by counting.
--
--   **Formalization Note** Item 1 is stated as `CanMeetIn (scale T z) x y i ↔ CanMeetIn (scale T z) 0 (x - y) i` for every $i$, and item 2 as `CanMeetIn (scale T z) 0 y i ↔ i = 1 + deg pb (z⁻¹ * y)` for every $i$: the round in which two distinct players can meet is unique, so this is the meaning of "$v = \dots$". The identities are stated for distinct players ($x \ne y$, $y \ne 0$), since the page leaves $d(0)$ and $v_T(x,x)$ undefined.
-- source:
--   Lambers, Pendavingh & Spieksma, How to Design a Stable Serial Knockout Competition, arXiv:2211.02513v1, p. 11, §3.3 (the two displayed identities before Theorem 3.1)

import Mathlib
import Definitions.Def_StableSKC_Galois_Model

namespace StableSKC.Galois
theorem scale_round_formula {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) (T : Seeding pb.dim F)
    (hT : ∀ x y : F, x ≠ y → CanMeetIn T x y (1 + deg pb (x - y))) (z : Fˣ) :
    (∀ x y : F, x ≠ y → ∀ i : ℕ,
      (CanMeetIn (scale T z) x y i ↔ CanMeetIn (scale T z) 0 (x - y) i)) ∧
    (∀ y : F, y ≠ 0 → ∀ i : ℕ,
      (CanMeetIn (scale T z) 0 y i ↔ i = 1 + deg pb ((↑z⁻¹ : F) * y))) := by sorry
end StableSKC.Galois
