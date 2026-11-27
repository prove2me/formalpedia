-- Prove2me | Theorems.Thm_StableSKC_Galois_Supplement_theorem_2_1
-- name    : StableSKC.Galois.Supplement.theorem_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T12:17:59.815196+00:00
-- url     : https://prove2.me/theorems/bc361e85-ec2e-4ab3-931c-1bea5eda2957
-- title:
--   Theorem 2.1, p. 7 — the seven node-line tournaments of a Fano-plane enumeration with x_r ∈ ℓ_r form a stable SKC on 8 players
-- statement:
--   Let the players $1, \dots, 7$ be the nodes of a Fano plane (player $0$ is not a node). Let $x_1, \dots, x_7$ be an enumeration of the seven nodes and $\ell_1, \dots, \ell_7$ an enumeration of the seven lines with $x_r \in \ell_r$ for every $r$, and let $T_r$ be a knockout tournament arising from the node-line pair $x_r, \ell_r$. Then $\mathcal T = \{T_1, \dots, T_7\}$ is a stable serial knockout competition on the $8 = 2^3$ players: it consists of $2^3 - 1 = 7$ tournaments, and for every pair of distinct players $x, x'$ and every round $i \in \{1, 2, 3\}$,
--   $$\#\{r : v_{T_r}(x, x') = i\} = 2^{i-1}.$$
--
--   This is the eight-player construction that the paper's general Theorem 3.1 extends to $2^k$ players through the Galois field $\mathrm{GF}(2^k)$; Table 1 is one instance.
--
--   **Formalization Note** The plane is any `S : RolesForceSeven.STS 7`, node `j` being player `j + 1 : Fin 8`. The enumerations are bijections `x : Fin 7 ≃ Fin 7` and `ℓ : Fin 7 ≃ S.lines`, indexed by $r = 0, \dots, 6$ instead of $1, \dots, 7$. The competition is the indexed family `T : Fin 7 → Seeding 3 (Fin 8)`, and the conclusion is the published `IsStableSKC T` together with the count (1) of the proof, `meetCount T a a' i = 2 ^ (i - 1)` for $1 \le i \le 3$.
--
--   Differences from the source:
--   - generalization: 𝒯 is stable → 𝒯 is a stable SKC (7 = 2^3 − 1 tournaments) and each count equals 2^{i−1} exactly; reason: the theorem's own proof establishes equation (1), and the SKC count is part of "the SKC defined by 𝒯"; the source's conclusion follows from the Lean one
--   - encoding: the Fano plane with nodes 1..7 → any Steiner triple system on Fin 7, node j ↦ player j + 1; reason: every STS on seven points is the Fano plane up to relabelling
--   - encoding: the set {T_1, …, T_7}, r = 1..7 → an indexed family over Fin 7; reason: the T_r are pairwise distinct (T_r places x_r at leaf 1), so the set and the family have the same members
--   - reading: "the knockout tournament that arises from x_r, ℓ_r" → any seeding satisfying the p. 6 construction; reason: the construction fixes the first pair as 0,x and leaves the order within the other pairs and of the second-half pairs free (p. 6 vs Table 1)
-- source:
--   Lambers, Pendavingh & Spieksma, How to Design a Stable Serial Knockout Competition, arXiv:2211.02513v1, p. 7, Theorem 2.1 and equation (1) of its proof

import Mathlib
import Definitions.Def_StableSKC_Galois_Model
import Definitions.Def_RolesForceSeven_sts
import Definitions.Def_StableSKC_Galois_Supplement_NodeLine

open RolesForceSeven

namespace StableSKC.Galois.Supplement
theorem theorem_2_1 (S : STS 7) (x : Fin 7 ≃ Fin 7) (ℓ : Fin 7 ≃ S.lines)
    (hxℓ : ∀ r : Fin 7, x r ∈ (ℓ r : Finset (Fin 7)))
    (T : Fin 7 → Seeding 3 (Fin 8)) (hT : ∀ r : Fin 7, ArisesFrom S (x r) (ℓ r) (T r)) :
    IsStableSKC T ∧
    ∀ a a' : Fin 8, a ≠ a' → ∀ i : ℕ, 1 ≤ i → i ≤ 3 → meetCount T a a' i = 2 ^ (i - 1) := by sorry
end StableSKC.Galois.Supplement
