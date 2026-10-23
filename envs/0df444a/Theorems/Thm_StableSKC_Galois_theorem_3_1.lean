-- Prove2me | Theorems.Thm_StableSKC_Galois_theorem_3_1
-- name    : StableSKC.Galois.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:25.719999+00:00
-- url     : https://prove2.me/theorems/f060cee4-c604-40ce-b14d-27de118957b6
-- title:
--   Theorem 3.1, p. 11 — {T(z) : z ∈ GF(2^k) ∖ {0}} is a stable SKC: each pair of players can meet in round i in exactly 2^{i−1} tournaments
-- statement:
--   Let $\mathrm{GF}(2^k)$ be presented as $\mathbb Z_2[X]/(q)$ for an irreducible $q$ of degree $k$ with root $\alpha$, let $d$ be the degree function with respect to the basis $1, \alpha, \dots, \alpha^{k-1}$, and let $T$ be a knockout tournament whose $2^k$ players are the elements of $\mathrm{GF}(2^k)$ and which satisfies Lemma 3.1:
--   $$v_T(x, y) = 1 + d(x - y) \quad \text{for all distinct } x, y \in \mathrm{GF}(2^k).$$
--   For nonzero $z$ let $T(z)$ be the tournament obtained from $T$ by replacing each player $x$ with $zx$. Then
--   $$\mathcal T := \{T(z) : z \text{ a nonzero element of } \mathrm{GF}(2^k)\}$$
--   is a stable serial knockout competition:
--
--   1. $\mathcal T$ consists of $2^k - 1$ knockout tournaments on the $2^k$ players;
--   2. for every pair of distinct players $x, x'$ and every round $i = 1, \dots, k$,
--   $$\#\{T \in \mathcal T : v_T(x, x') = i\} = 2^{i-1}.$$
--
--   This is the paper's main result: stable serial knockout competitions exist for every number of players $n = 2^k$, and they are obtained explicitly from the multiplicative group of $\mathrm{GF}(2^k)$. The count $2^{i-1}$ is the only possible stable value, since a player can meet $2^{i-1}$ opponents in round $i$ of any single tournament.
--
--   **Formalization Note** The family is indexed by the units `z : Fˣ` of a field `F` with a power basis `pb` over `ZMod 2` of dimension $k$ = `pb.dim`. `IsStableSKC` includes that the index set has $2^k - 1$ elements; the explicit count $2^{i-1}$ is stated as a second conclusion (the proof on p. 11 prints $2^i$, a misprint; p. 4 gives $c_i = 2^{i-1}$). The hypothesis on $T$ is required for distinct players only, since $d(0)$ is undefined on the page; Lemma 3.1 shows it is satisfiable. No assumption $k \ge 2$ is made, as Theorem 3.1 does not need it.
-- source:
--   Lambers, Pendavingh & Spieksma, How to Design a Stable Serial Knockout Competition, arXiv:2211.02513v1, p. 11, Theorem 3.1 (with the standing hypothesis of §3.3, p. 11, and Definitions 1.1–1.3, pp. 3–4)

import Mathlib
import Definitions.Def_StableSKC_Galois_Model

namespace StableSKC.Galois
theorem theorem_3_1 {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
    (pb : PowerBasis (ZMod 2) F) (T : Seeding pb.dim F)
    (hT : ∀ x y : F, x ≠ y → CanMeetIn T x y (1 + deg pb (x - y))) :
    IsStableSKC (fun z : Fˣ => scale T z) ∧
    ∀ x x' : F, x ≠ x' → ∀ i : ℕ, 1 ≤ i → i ≤ pb.dim →
      meetCount (fun z : Fˣ => scale T z) x x' i = 2 ^ (i - 1) := by sorry
end StableSKC.Galois
