-- Prove2me | Theorems.Thm_PCNonBool_theorem_5_1_no_fail
-- name    : PCNonBool.theorem_5_1_no_fail
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:04.230894+00:00
-- url     : https://prove2.me/theorems/6fedda15-7363-4cd7-9e9b-408dadc01f70
-- title:
--   Proof of Theorem 5.1 — Algorithm 1 does not output FAIL (removing a pigeon and two holes costs expansion at most 2)
-- statement:
--   **From the proof of Theorem 5.1: Algorithm 1 does not output FAIL.** Let $G=(U\sqcup V,E)$ be an $(s,\Delta,c)$-boundary expander with $|U|>|V|$ and $c\ge5$, and $\tau=s/(10(2\Delta+3))$.
--
--   1. For all $U_a\subseteq U$, $V_a\subseteq V$, $c'\in\mathbb R$, $i\in U_a$ and $j,j'\in V_a$: if $G[U_a\sqcup V_a]$ is an $(s,\Delta,c')$-boundary expander, then $G[(U_a\setminus\{i\})\sqcup(V_a\setminus\{j,j'\})]$ is an $(s,\Delta,c'-2)$-boundary expander. In particular, if $G_{\ell-1}$ is an $(s,\Delta,c-1)$-boundary expander then $G'_\ell$ is an $(s,\Delta,c-3)$-boundary expander, so the test at line 18 never fires.
--   2. Every partial run of Algorithm 1 with $L<\lfloor\tau\rfloor$ rounds can be extended by one more round.
--
--   Differences from the source:
--   - generalization: if G_{ℓ−1} is an (s, Δ, c − 1)-boundary expander then G′_ℓ is an (s, Δ, c − 3)-boundary expander → for every instance (Ua, Va), every c′ ∈ ℝ, every i ∈ Ua and j, j′ ∈ Va: (s, Δ, c′)-expansion of G[Ua ⊔ Va] gives (s, Δ, c′ − 2)-expansion of G[(Ua \ {i}) ⊔ (Va \ {j, j′})]; reason: the source's sentence is the case c′ = c − 1, (Ua, Va) = (U_{ℓ−1}, V_{ℓ−1}) and (i, j, j′) the split triple
--   - reading: "Algorithm 1 does not output FAIL" → additionally: every partial run of L < ⌊τ⌋ rounds has a next round (a split triple, an inclusion-maximal S_ℓ and a matching M_ℓ exist); reason: with the algorithm as a relation, "does not fail" means that the loop can always continue; the paper's line 21 relies on Proposition 5.11 for the matching
--   - reading: Algorithm 1 (p.30): "find" a most frequently touching triple, "maximal set" S_ℓ, "assignment induced by matching M_ℓ", for 1 ≤ ℓ ≤ τ → Step/IsRun: every run of ⌊τ⌋ rounds with any maximizing triple, any inclusion-maximal S_ℓ, any matching M_ℓ and the matching assignment of stepAssignment; the statement holds for every such run; reason: the algorithm leaves these choices open; the paper's claims are about whatever choices are made, and inclusion-maximal covers cardinality-maximal
--   - encoding: G_ℓ = G[U_ℓ ⊔ V_ℓ] and FPHP(G_ℓ) over its own variables → sub-instances are vertex sets (U_ℓ, V_ℓ) inside G: IsBoundaryExpanderOn, fphpOn, ppHighOn, with polynomials in the ring of all edge variables of G; reason: π_ℓ only mentions edges of G_ℓ; the edge variables outside G_ℓ carry no axiom and do not occur
--   - generalization: Algorithm 1's header assumption |π| < exp(Dτ/(2Δ²N)) → no size assumption on π; reason: the claim does not use it; the size bound is used only in the final calculation of the proof of Theorem 5.1
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), proof of Theorem 5.1 (Algorithm 1 does not output FAIL), p.31 (PDF p.34)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_IsBoundaryExpanderOn
import Definitions.Def_PCNonBool_IsBoundaryExpander
import Definitions.Def_PCNonBool_tau
import Definitions.Def_PCNonBool_AlgState
import Definitions.Def_PCNonBool_Step
import Definitions.Def_PCNonBool_IsRun

namespace PCNonBool

/-- **Proof of Theorem 5.1**, "Algorithm 1 does not output FAIL" (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.31 (PDF p.34)):
"if `G_{ℓ-1}` is a `(s, Δ, c - 1)`-boundary expander, then `G'_ℓ` is a `(s, Δ, c - 3)`-boundary
expander". Stated for every instance: deleting a pigeon `i` and two holes `j, j'` from an
`(s, Δ, c')`-boundary expander leaves an `(s, Δ, c' - 2)`-boundary expander. Second clause: in
every partial run of Algorithm 1 with fewer than `⌊τ⌋` rounds, a further round exists.

**Formalization Note** The algorithm is a relation (`Step`), so "does not fail" is stated as the
existence of the next round. The header hypotheses on `G` are kept; `π` is arbitrary. -/
theorem theorem_5_1_no_fail {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (s Δ : ℕ) (c D : ℝ) (hc : 5 ≤ c) (hN : Fintype.card V < Fintype.card U)
    (hG : IsBoundaryExpander G s Δ c) (π : List (MvPolynomial (Var G) F)) :
    (∀ (Ua : Finset U) (Va : Finset V) (c' : ℝ) (i : U) (j j' : V),
        IsBoundaryExpanderOn G Ua Va s Δ c' → i ∈ Ua → j ∈ Va → j' ∈ Va →
        IsBoundaryExpanderOn G (Ua.erase i) (Va \ {j, j'}) s Δ (c' - 2)) ∧
    ∀ L < ⌊tau s Δ⌋₊, ∀ st : ℕ → AlgState (F := F) G, IsRun G s c D π L st →
      ∃ st' : AlgState (F := F) G, Step G s c D (st L) st' := by sorry

end PCNonBool
