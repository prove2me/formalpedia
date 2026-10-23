-- Prove2me | Theorems.Thm_StableSKC_Galois_scale_canMeetIn
-- name    : StableSKC.Galois.scale_canMeetIn
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:29.726512+00:00
-- url     : https://prove2.me/theorems/14c1db4a-2e55-4992-ba44-2fb52640ba6e
-- title:
--   §3.3, p. 11 — relabelling by z: v_{T(z)}(x, y) = v_T(z^{−1}x, z^{−1}y)
-- statement:
--   Let $T$ be a knockout tournament on $2^k$ players whose players are the elements of a field $F$, let $z \in F$ be nonzero, and let $T(z)$ be the tournament obtained from $T$ by replacing each player $x$ with $zx$. Then for all players $x, y$ and every round $i$,
--   $$v_{T(z)}(x, y) = i \iff v_T(z^{-1}x, z^{-1}y) = i .$$
--   In words: $x$ and $y$ can meet in round $i$ of $T(z)$ exactly when $z^{-1}x$ and $z^{-1}y$ can meet in round $i$ of $T$, because $x$ sits in $T(z)$ at the leaf where $z^{-1}x$ sits in $T$.
--
--   This transports the meeting rounds of $T$ to every relabelled tournament $T(z)$ and is the first step of the computation in §3.3.
--
--   **Formalization Note** $v_{T}(x,y) = i$ is the predicate `CanMeetIn T x y i`, and the identity of the page is stated as an equivalence of these predicates for every $i$.
-- source:
--   Lambers, Pendavingh & Spieksma, How to Design a Stable Serial Knockout Competition, arXiv:2211.02513v1, p. 11, §3.3

import Mathlib
import Definitions.Def_StableSKC_Galois_Model

namespace StableSKC.Galois
theorem scale_canMeetIn {k : ℕ} {F : Type*} [Field F] (T : Seeding k F) (z : Fˣ) (x y : F)
    (i : ℕ) :
    CanMeetIn (scale T z) x y i ↔ CanMeetIn T ((↑z⁻¹ : F) * x) ((↑z⁻¹ : F) * y) i := by sorry
end StableSKC.Galois
