-- Prove2me | Theorems.Thm_RandGraphStates_corollary_4_2
-- name    : RandGraphStates.corollary_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:02:17.211245+00:00
-- url     : https://prove2.me/theorems/a4a69aef-a4a4-4cec-9237-074544184543
-- title:
--   Corollary 4.2: $\alpha_{\mathrm{LC}}$ is a maximum nullity
-- statement:
--   For every simple graph $G$ on a finite vertex set,
--   $$
--   \alpha_{\mathrm{LC}}(G)=\max_{S\subseteq V(G)}\ \max_{D\in\mathcal D(S)}\mathrm{Nullity}\bigl(A_G[S]+D\bigr),
--   $$
--   where $A_G[S]$ is the principal submatrix of the adjacency matrix over $\mathbb F_2$ on $S$ and $\mathcal D(S)$ is the set of diagonal matrices on $S$ with entries in $\{0,1\}$.
--
--   This turns the orbit parameter $\alpha_{\mathrm{LC}}$ into a problem about nullities of principal submatrices, which is the form used by both bounds on $\alpha_{\mathrm{LC}}(G_{n,p})$.
--
--   Differences from the source:
--   - encoding: max over S and D → IsGreatest of the set of values over S and d; reason: the same value; no junk value of a supremum is involved
--   - encoding: every simple graph → a graph on a finite vertex type V; reason: graphs in the paper are finite (§2)
-- source:
--   Chen, Ferber, Goodenough, Sales, Entanglement in random graph states, manuscript (November 2026), Corollary 4.2, p.18

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting
import Definitions.Def_RandGraphStates_alphaLC
import Definitions.Def_SquashedKey_KeyBoundFunction
import Definitions.Def_RandGraphStates_cEtaEps
import Definitions.Def_RandGraphStates_pMinus
import Definitions.Def_RandGraphStates_Cunif
import Definitions.Def_RandGraphStates_nullity
import Definitions.Def_RandGraphStates_piTail

set_option autoImplicit false

open BollobasChromatic.Main
open Filter Topology

namespace RandGraphStates

/-- **Corollary 4.2** (nullity characterization). For every simple graph `G`,
`αLC(G) = max_{S ⊆ V(G)} max_{D ∈ D(S)} Nullity(A_G[S] + D)`.

Source: Chen, Ferber, Goodenough, Sales, *Entanglement in random graph states*, manuscript (November 2026), Corollary 4.2, p.18.

**Formalization Note.** The double maximum is written with `IsGreatest`, so nothing depends on a
junk value. `S = ∅` is admitted, with nullity `0`. -/
theorem corollary_4_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    IsGreatest
      {k : ℕ | ∃ (S : Finset V) (d : S → ZMod 2),
        k = nullity ((adjF2 G).submatrix ((↑) : S → V) ((↑) : S → V) + Matrix.diagonal d)}
      (alphaLC G) := by sorry

end RandGraphStates
