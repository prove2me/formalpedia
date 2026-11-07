-- Prove2me | Theorems.Thm_PCNonBool_lemma_5_13
-- name    : PCNonBool.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:22.352321+00:00
-- url     : https://prove2.me/theorems/b9dbe131-cdb8-4d95-8a41-66a23bc41dad
-- title:
--   Lemma 5.13 — $\pi_\ell$ is a polynomial calculus refutation of FPHP$(G_\ell)$
-- statement:
--   **Lemma 5.13.** Let $\mathbb F$ be a field of characteristic different from $2$ and $G=(U\sqcup V,E)$ an $(s,\Delta,c)$-boundary expander with $|U|>|V|$ and $c\ge5$. Run Algorithm 1 on a polynomial calculus refutation $\pi$ of FPHP$(G)$. Then for every $0\le\ell\le\lfloor\tau\rfloor$, the sequence $\pi_\ell$ is a polynomial calculus refutation of FPHP$(G_\ell)$, where $G_\ell=G[U_\ell\sqcup V_\ell]$.
--
--   Together with Proposition 5.12 this says that every round turns a refutation on an expander into a refutation on a smaller expander.
--
--   Differences from the source:
--   - reading: Algorithm 1 (p.30): "find" a most frequently touching triple, "maximal set" S_ℓ, "assignment induced by matching M_ℓ", for 1 ≤ ℓ ≤ τ → Step/IsRun: every run of ⌊τ⌋ rounds with any maximizing triple, any inclusion-maximal S_ℓ, any matching M_ℓ and the matching assignment of stepAssignment; the statement holds for every such run; reason: the algorithm leaves these choices open; the paper's claims are about whatever choices are made, and inclusion-maximal covers cardinality-maximal
--   - encoding: G_ℓ = G[U_ℓ ⊔ V_ℓ] and FPHP(G_ℓ) over its own variables → sub-instances are vertex sets (U_ℓ, V_ℓ) inside G: IsBoundaryExpanderOn, fphpOn, ppHighOn, with polynomials in the ring of all edge variables of G; reason: π_ℓ only mentions edges of G_ℓ; the edge variables outside G_ℓ carry no axiom and do not occur
--   - generalization: Algorithm 1's header assumption |π| < exp(Dτ/(2Δ²N)) → no size assumption on π; reason: the claim does not use it; the size bound is used only in the final calculation of the proof of Theorem 5.1
--   - reading: polynomial calculus (refutations on both sides of the statement) → the mission's PC model on both sides: lines reduced modulo the range axioms, axiom lines c·red(a) with c ∈ F, fan-in 2, refutation = derivation containing 1; reason: one PC model is used throughout the mission; it is the model the paper's own splitting and restriction steps (Lemmas 5.9, 5.13) need
--   - encoding: lines of a refutation represented in the quotient ring modulo the range axioms (p.11); size = number of monomials → lines are the multilinear representatives (redPM / redBool normal forms); the multiplication rule reduces its result; size counts their monomials; reason: the paper's own convention (p.11); it only strengthens size and degree lower bounds
--   - encoding: refutation = derivation of the constant polynomial 1 → IsRefutation: a derivation that contains the line 1; reason: cutting a sequence after its first 1 gives a refutation in the paper's sense of no larger size or degree
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Lemma 5.13, p.30 (PDF p.33)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_IsBoundaryExpander
import Definitions.Def_PCNonBool_redPM
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_fphpOn
import Definitions.Def_PCNonBool_fphp
import Definitions.Def_PCNonBool_tau
import Definitions.Def_PCNonBool_AlgState
import Definitions.Def_PCNonBool_IsRun

namespace PCNonBool

/-- **Lemma 5.13** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.30 (PDF p.33)). For `0 ≤ ℓ ≤ τ` and `π_ℓ`, `G_ℓ` as in Algorithm 1,
`π_ℓ` is a polynomial calculus refutation of FPHP(G_ℓ).

**Formalization Note** Algorithm 1 runs on a refutation `π` of FPHP(G) under its header
hypotheses; the statement holds for every run. `FPHP(G_ℓ)` is `fphpOn G U_ℓ V_ℓ` in the ring of
all edge variables of `G`. The refutations are in the mission's PC model: splitting and
restricting turn axioms into scalar multiples of axioms (e.g. `2^k` times a shortened (33b)) or
into `0`. -/
theorem lemma_5_13 {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] (hF : ringChar F ≠ 2)
    (G : BipGraph U V) (s Δ : ℕ) (c D : ℝ) (hc : 5 ≤ c) (hN : Fintype.card V < Fintype.card U)
    (hG : IsBoundaryExpander G s Δ c) (π : List (MvPolynomial (Var G) F))
    (hπ : IsRefutation redPM (fphp G) π)
    (st : ℕ → AlgState (F := F) G) (hrun : IsRun G s c D π ⌊tau s Δ⌋₊ st)
    (ℓ : ℕ) (hℓ : ℓ ≤ ⌊tau s Δ⌋₊) :
    IsRefutation redPM (fphpOn G (st ℓ).Ua (st ℓ).Va) (st ℓ).π := by sorry

end PCNonBool
