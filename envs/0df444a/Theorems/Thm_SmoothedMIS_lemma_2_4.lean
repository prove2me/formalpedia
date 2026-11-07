-- Prove2me | Theorems.Thm_SmoothedMIS_lemma_2_4
-- name    : SmoothedMIS.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:23.234102+00:00
-- url     : https://prove2.me/theorems/7754a02a-84c2-48a3-bb48-fcd90b93c479
-- title:
--   Lemma 2.4 — Gathering: $r+1$ rounds, deterministic, never wrong, complete within distance $r$
-- statement:
--   Let $H$ be a finite graph with distinct identifiers, let $A\subseteq V(H)$ be known to its members, and let $r\ge1$ be an integer. The procedure $\mathrm{Gather}(H,A,r)$ takes $r+1$ rounds, its outputs do not depend on the random bits, and for every $v\in A$:
--   1. if $v$ outputs a graph, this graph is $C_v$, the component of $H[A]$ containing $v$ (labelled by identifiers);
--   2. if every vertex of $C_v$ is within distance $r$ of $v$ in $H$, then $v$ outputs $C_v$.
--
--   Algorithm 1 uses this with $H=\mathcal G$, $A=\mathcal A$ and $r=\ell$; clause 1 makes $J$ independent and clause 2 makes it dominate $\mathcal A$ under condition (1).
--
--   Differences from the source:
--   - encoding: the procedure "is deterministic" → the output of every node is the same for all random tapes; reason: the procedure is run inside the randomized model, where determinism means independence from the tapes
--   - encoding: outputs either a graph or the symbol ⊥; the graph C_v → Option LGraph; C_v as the identifier-labelled graph labComp; reason: the vertices of C_v are known to v only through their identifiers
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), Lemma 2.4, p.10, procedure p.11 (PDF pp.12–13)

import Mathlib
import Definitions.Def_SmoothedMIS_gatherAlg

namespace SmoothedMIS

/-- **Lemma 2.4 (Gathering)** (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed Analysis for
Distributed MIS* (manuscript, sha256 dc2131db…), Lemma 2.4, p.10, procedure p.11). Let `H` be a
graph with distinct identifiers, `A ⊆ V(H)` known to every vertex, and `r ≥ 1`. The procedure
`Gather(H, A, r)` is deterministic and takes `r + 1` rounds; at its end every `v ∈ A` outputs a
graph or `⊥`, and (i) if `v` outputs a graph, this graph is `C_v` (the component of `H[A]`
containing `v`); (ii) if every vertex of `C_v` is within distance `r` of `v` in `H`, then `v`
outputs `C_v`.

**Formalization Note** `gatherAlg r` implements the procedure of p.11 in the LOCAL model of
`LocalAlg`; graphs are output labelled by identifiers (`labComp`). "Deterministic" is the
independence of the output from the random tapes. Distances are `SimpleGraph.edist`. -/
theorem lemma_2_4 {V : Type} [Fintype V] (H : SimpleGraph V) (A : Set V) (ids : V → ℕ)
    (hids : Function.Injective ids) (r : ℕ) (hr : 1 ≤ r) :
    (gatherAlg r).rounds () = r + 1 ∧
    (∀ (tape tape' : V → ℕ → Bool) (v : V),
      gatherOut H A ids r tape v = gatherOut H A ids r tape' v) ∧
    ∀ (tape : V → ℕ → Bool), ∀ v ∈ A,
      (∀ C, gatherOut H A ids r tape v = some C → C = labComp H A ids v) ∧
      ((∀ u ∈ compSet H A v, H.edist v u ≤ r) →
        gatherOut H A ids r tape v = some (labComp H A ids v)) := by sorry

end SmoothedMIS
