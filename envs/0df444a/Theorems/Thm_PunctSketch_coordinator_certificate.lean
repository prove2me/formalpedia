-- Prove2me | Theorems.Thm_PunctSketch_coordinator_certificate
-- name    : PunctSketch.coordinator_certificate
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:46:15.8752+00:00
-- url     : https://prove2.me/theorems/4710fe2a-a3eb-4787-8970-608e0bc2607d
-- title:
--   §5.4, pp.21–22 — on $\mathcal E$ the output $H$ is a certificate
-- statement:
--   Let $1\le k<n$, and suppose $\mathcal T(F)$ is a spanning forest of $G\setminus F$ for every $|F|<k$. Along any run of the coordinator's procedure, for any pair order and any choices in steps 2 and 4: no failure is reported and $H\le G$. When all pairs are done, for every $|F|<k$ two vertices are connected in $H\setminus F$ exactly when they are connected in $G\setminus F$, and
--   $$H\text{ is }k\text{-connected}\iff G\text{ is }k\text{-connected}.$$
--
--   Differences from the source:
--   - generalization: 𝒯(F) the output of the spanning-forest procedure on the stored sketches → any oracle 𝒯 with 𝒯(F) a spanning forest of G ⧵ F for all |F| < k; reason: this is event ℰ, and all the argument uses of it
--   - generalization: "H[V ⧵ F] and G ⧵ F have the same number of connected components" → the two connectivity relations coincide; reason: with H ≤ G they are equivalent, and the relation is what the printed argument proves
--   - encoding: the procedure, steps 1–4 → a transition relation, with any pair order, any minimum separator and any suitable edge; reason: every run of the printed procedure is a run of the relation
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §5.4, pp.21–22 (PDF pp.22–23)

import Mathlib
import Definitions.Def_Balinski61_Connectivity_TuplyConnected
import Definitions.Def_PunctSketch_CoordStep

namespace PunctSketch

/-- **The §5.4 output is a certificate on ℰ.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §5.4, pp.21–22: "H[V ⧵ F] and G ⧵ F have the same
number of connected components for all F ⊆ V, |F| < k"; "When ℰ occurs, neither failure happens, and
H[V ⧵ F] and G ⧵ F have the same number of connected components for every |F| < k. Hence, H is
k-vertex-connected if and only if G is."

If `𝒯(F)` is a spanning forest of `G ∖ F` for all `|F| < k`, then along any run of the procedure (any
pair order, any minimum separator, any edge in step 4): no failure is reported, `H ≤ G`, and when all
pairs are done `H ∖ F` and `G ∖ F` have the same connectivity for all `|F| < k`, and `H` is `k`-connected
if and only if `G` is.

**Formalization Note.** The agreement is stated on the connectivity relation, which with `H ≤ G` is the
same as the printed equal number of components. -/
theorem coordinator_certificate {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) (G : SimpleGraph (Fin n))
    (𝒯 : Finset (Fin n) → Option (Finset (Sym2 (Fin n))))
    (h𝒯 : ∀ F : Finset (Fin n), F.card < k → ∃ T, 𝒯 F = some T ∧ IsSpanningForestOf G F T)
    (pairs : List (Fin n × Fin n)) (hpairs : IsPairOrder pairs) (s : CoordState n)
    (hrun : Relation.ReflTransGen (CoordStep 𝒯 k) (coordInit pairs) s) :
    s.failed = false ∧ s.H ≤ G ∧
      (s.pairs = [] →
        (∀ F : Finset (Fin n), F.card < k → ∀ x y, ConnAvoid s.H F x y ↔ ConnAvoid G F x y) ∧
        (Balinski61.Connectivity.IsNTuplyConnected s.H k ↔
          Balinski61.Connectivity.IsNTuplyConnected G k)) := by sorry

end PunctSketch
