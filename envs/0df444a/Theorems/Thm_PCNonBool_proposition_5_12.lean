-- Prove2me | Theorems.Thm_PCNonBool_proposition_5_12
-- name    : PCNonBool.proposition_5_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:28.205898+00:00
-- url     : https://prove2.me/theorems/23fd097a-24f5-4246-8377-dce532aefcdd
-- title:
--   Proposition 5.12 (corrected: strictness needs $s \ge 1$) — $|C_\ell| \le 2\tau$ and $G_\ell$ is an $(s,\Delta,c-1)$-boundary expander
-- statement:
--   **Proposition 5.12.** Let $G=(U\sqcup V,E)$ be an $(s,\Delta,c)$-boundary expander with $|U|=N>n=|V|$ and $c\ge5$, let $\tau=s/(10(2\Delta+3))$, and consider any run of Algorithm 1 on $G$. For every $0\le\ell\le\lfloor\tau\rfloor$:
--
--   1. the set $C_\ell=\bigcup_{\ell'\le\ell}S_{\ell'}$ has size at most $2\tau$, and if $s\ge1$ it is strictly smaller than $s$;
--   2. the graph $G_\ell=G[U_\ell\sqcup V_\ell]$ is an $(s,\Delta,c-1)$-boundary expander.
--
--   Expansion of $G_\ell$ is what keeps Corollary 5.4 applicable to the final graph $G_\tau$.
--
--   Differences from the source:
--   - correction: |C_ℓ| ≤ 2τ "(and hence strictly smaller than s)" → |C_ℓ| ≤ 2τ, and |C_ℓ| < s when s ≥ 1; reason: for s = 0, τ = 0 and |C_0| = 0 is not < 0
--   - reading: Algorithm 1 (p.30): "find" a most frequently touching triple, "maximal set" S_ℓ, "assignment induced by matching M_ℓ", for 1 ≤ ℓ ≤ τ → Step/IsRun: every run of ⌊τ⌋ rounds with any maximizing triple, any inclusion-maximal S_ℓ, any matching M_ℓ and the matching assignment of stepAssignment; the statement holds for every such run; reason: the algorithm leaves these choices open; the paper's claims are about whatever choices are made, and inclusion-maximal covers cardinality-maximal
--   - encoding: G_ℓ = G[U_ℓ ⊔ V_ℓ] and FPHP(G_ℓ) over its own variables → sub-instances are vertex sets (U_ℓ, V_ℓ) inside G: IsBoundaryExpanderOn, fphpOn, ppHighOn, with polynomials in the ring of all edge variables of G; reason: π_ℓ only mentions edges of G_ℓ; the edge variables outside G_ℓ carry no axiom and do not occur
--   - generalization: Algorithm 1's input π, a refutation of FPHP(G) with |π| < exp(Dτ/(2Δ²N)) → any finite list π of polynomials; reason: the claim concerns only the graphs G_ℓ and the sets C_ℓ, whose evolution does not depend on π being a refutation or small
--   - generalization: Algorithm 1 stops with FAIL at line 18 when G′_ℓ is not an (s, Δ, 2)-boundary expander → Step has no FAIL test; runs continue; reason: covers every run of the paper's algorithm (which never fails, by the proof of Theorem 5.1) and more
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Proposition 5.12, p.30 (PDF p.33)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_IsBoundaryExpanderOn
import Definitions.Def_PCNonBool_IsBoundaryExpander
import Definitions.Def_PCNonBool_tau
import Definitions.Def_PCNonBool_AlgState
import Definitions.Def_PCNonBool_IsRun

namespace PCNonBool

/-- **Proposition 5.12** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.30 (PDF p.33)), corrected. Let `G` be an `(s, Δ, c)`-boundary
expander with `|U| > |V|` and `c ≥ 5` (Algorithm 1's header). For every run of Algorithm 1 and
every `0 ≤ ℓ ≤ ⌊τ⌋`:

1. `C_ℓ = ⋃_{ℓ' ≤ ℓ} S_ℓ'` has size at most `2τ`, and (when `s ≥ 1`) strictly less than `s`;
2. `G_ℓ = G[U_ℓ ⊔ V_ℓ]` is an `(s, Δ, c - 1)`-boundary expander.

**Formalization Note** "Strictly smaller than `s`" fails at `s = 0` (`|C_0| = 0`). The input `π` is
arbitrary: the claim concerns only the graphs. -/
theorem proposition_5_12 {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (s Δ : ℕ) (c D : ℝ) (hc : 5 ≤ c) (hN : Fintype.card V < Fintype.card U)
    (hG : IsBoundaryExpander G s Δ c) (π : List (MvPolynomial (Var G) F))
    (st : ℕ → AlgState (F := F) G) (hrun : IsRun G s c D π ⌊tau s Δ⌋₊ st)
    (ℓ : ℕ) (hℓ : ℓ ≤ ⌊tau s Δ⌋₊) :
    ((st ℓ).C.card : ℝ) ≤ 2 * tau s Δ ∧ (1 ≤ s → (st ℓ).C.card < s) ∧
      IsBoundaryExpanderOn G (st ℓ).Ua (st ℓ).Va s Δ (c - 1) := by sorry

end PCNonBool
