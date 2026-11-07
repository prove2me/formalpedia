-- Prove2me | Theorems.Thm_PCNonBool_lemma_5_14
-- name    : PCNonBool.lemma_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:17.573025+00:00
-- url     : https://prove2.me/theorems/882a15ae-1de8-4745-82ac-b4ff64a4e3c5
-- title:
--   Lemma 5.14 (corrected: $\mathrm{PPHigh}_D(\pi_{\ell-1}) \ne \emptyset$) — each round shrinks $|\mathrm{PPHigh}_D|$ by a factor $1 - D/(\Delta N)$
-- statement:
--   **Lemma 5.14.** Let $\mathbb F$ be a field of characteristic different from $2$, $G=(U\sqcup V,E)$ an $(s,\Delta,c)$-boundary expander with $|U|=N>|V|$ and $c\ge5$, and $D\in\mathbb R$. Run Algorithm 1 on a refutation $\pi$ of FPHP$(G)$. For every $1\le\ell\le\lfloor\tau\rfloor$ with $\mathrm{PPHigh}_D(\pi_{\ell-1})\ne\emptyset$,
--   $$|\mathrm{PPHigh}_D(\pi_\ell)|\ <\ \Bigl(1-\frac{D}{\Delta N}\Bigr)\,|\mathrm{PPHigh}_D(\pi_{\ell-1})|,$$
--   where pairwise pigeon degree is measured in $G_\ell$ on the left and in $G_{\ell-1}$ on the right, and $N$ is the number of pigeons of FPHP$(G)$.
--
--   Iterated over $\lfloor\tau\rfloor$ rounds this forces $|\mathrm{PPHigh}_D(\pi)|$ to be exponentially large unless $\mathrm{PPHigh}_D(\pi_\tau)$ is empty.
--
--   Differences from the source:
--   - correction: no condition on PPHigh_D(π_{ℓ−1}) → PPHigh_D(π_{ℓ−1}) ≠ ∅; reason: Algorithm 1 takes D as an input: for D > N every pair has ppdeg ≤ N < D, both sides are 0 and 0 < 0 fails; for D ≤ 0 the condition holds automatically (the line 1 gives the pair (1, 1)) and the printed strict inequality holds, since every nonzero axiom line of FPHP(G_{ℓ−1}) has a touched pair such as (1, x_{i,j}); the proof of Theorem 5.1 uses D = (c − 1)s/(12Δ) while PPHigh_D is nonempty
--   - reading: PPHigh_D(π_ℓ) and PPHigh_D(π_{ℓ−1}) (Definition 5.5 for "G") → PPHigh_D(π_ℓ) measured in G_ℓ = G[U_ℓ ⊔ V_ℓ], PPHigh_D(π_{ℓ−1}) in G_{ℓ−1}; reason: the proof works modulo I_{ℓ−1} = ⟨PA(G_{ℓ−1}) ∪ range⟩, and π_ℓ refutes FPHP(G_ℓ) (Lemma 5.13)
--   - reading: ppdeg(m₀, m₁) = pdeg of the unique minimum-degree monomial in the class of m₀m₁ modulo ⟨PA ∪ {x² − 1}⟩ (Definition 5.5) → ppdegOn counts the pigeons i whose set H of holes occurring to an odd power in m₀m₁ is neither ∅ nor N(i); reason: the minimum-degree representative is not unique when |H| = |N(i)|/2, but whether pigeon i is mentioned is the same for every representative; when some pigeon has no hole the ideal is the unit ideal and the pigeon-by-pigeon count is still the Q-degree of Definition 4.9 (Proposition 5.6)
--   - reading: Algorithm 1 (p.30): "find" a most frequently touching triple, "maximal set" S_ℓ, "assignment induced by matching M_ℓ", for 1 ≤ ℓ ≤ τ → Step/IsRun: every run of ⌊τ⌋ rounds with any maximizing triple, any inclusion-maximal S_ℓ, any matching M_ℓ and the matching assignment of stepAssignment; the statement holds for every such run; reason: the algorithm leaves these choices open; the paper's claims are about whatever choices are made, and inclusion-maximal covers cardinality-maximal
--   - encoding: G_ℓ = G[U_ℓ ⊔ V_ℓ] and FPHP(G_ℓ) over its own variables → sub-instances are vertex sets (U_ℓ, V_ℓ) inside G: IsBoundaryExpanderOn, fphpOn, ppHighOn, with polynomials in the ring of all edge variables of G; reason: π_ℓ only mentions edges of G_ℓ; the edge variables outside G_ℓ carry no axiom and do not occur
--   - generalization: Algorithm 1's header assumption |π| < exp(Dτ/(2Δ²N)) → no size assumption on π; reason: the claim does not use it; the size bound is used only in the final calculation of the proof of Theorem 5.1
--   - generalization: polynomial calculus: axiom lines are axioms of P → an axiom line may be any scalar multiple c·red(a) of a reduced axiom a ∈ P, c = 0 allowed; reason: every standard refutation is one of these, so a lower bound over this larger system implies the paper's; the paper's own Lemmas 5.9 and 5.13 produce scaled axiom lines
--   - encoding: lines of a refutation represented in the quotient ring modulo the range axioms (p.11); size = number of monomials → lines are the multilinear representatives (redPM / redBool normal forms); the multiplication rule reduces its result; size counts their monomials; reason: the paper's own convention (p.11); it only strengthens size and degree lower bounds
--   - encoding: variables x_{i,j}, i ∈ U, j ∈ N(i); x_{i,j} = −1 iff pigeon i flies to hole j → variables indexed by the edges of G (Var G); bipartite graph = finite types U, V with a decidable adjacency relation; reason: Lean convention; same instances
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Lemma 5.14, (41), p.31 (PDF p.34)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_Var
import Definitions.Def_PCNonBool_IsBoundaryExpander
import Definitions.Def_PCNonBool_redPM
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_PCNonBool_fphp
import Definitions.Def_PCNonBool_ppHighOn
import Definitions.Def_PCNonBool_tau
import Definitions.Def_PCNonBool_AlgState
import Definitions.Def_PCNonBool_IsRun

namespace PCNonBool

/-- **Lemma 5.14** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), (41), p.31 (PDF p.34)), corrected. For `1 ≤ ℓ ≤ τ` and `π_ℓ` as in
Algorithm 1, `|PPHigh_D(π_ℓ)| < (1 - D/(ΔN)) |PPHigh_D(π_{ℓ-1})|`, where `N` is the number of
pigeons of FPHP(G), provided `PPHigh_D(π_{ℓ-1})` is nonempty.

**Formalization Note** Without the proviso the strict inequality fails: for `D > N` every pair has
`ppdeg ≤ N < D` and both sides are `0`. For `D ≤ 0` the proviso holds automatically (the line `1`
gives the pair `(1, 1)`), and the strict inequality holds because every nonzero axiom line of
FPHP(G_{ℓ-1}) has a touched pair such as `(1, x_{i,j})`. `PPHigh_D(π_ℓ)` is measured in `G_ℓ` and
`PPHigh_D(π_{ℓ-1})` in `G_{ℓ-1}`, as in the proof (ideal `I_{ℓ-1}`). `Δ` and `N = |U|` are those of
the original graph. -/
theorem lemma_5_14 {F : Type*} [Field F] {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V] (hF : ringChar F ≠ 2)
    (G : BipGraph U V) (s Δ : ℕ) (c D : ℝ) (hc : 5 ≤ c) (hN : Fintype.card V < Fintype.card U)
    (hG : IsBoundaryExpander G s Δ c) (π : List (MvPolynomial (Var G) F))
    (hπ : IsRefutation redPM (fphp G) π)
    (st : ℕ → AlgState (F := F) G) (hrun : IsRun G s c D π ⌊tau s Δ⌋₊ st)
    (ℓ : ℕ) (hℓ₁ : 1 ≤ ℓ) (hℓ : ℓ ≤ ⌊tau s Δ⌋₊)
    (hne : (ppHighOn G (st (ℓ - 1)).Ua (st (ℓ - 1)).Va D (st (ℓ - 1)).π).Nonempty) :
    ((ppHighOn G (st ℓ).Ua (st ℓ).Va D (st ℓ).π).card : ℝ) <
      (1 - D / ((Δ : ℝ) * (Fintype.card U : ℝ))) *
        ((ppHighOn G (st (ℓ - 1)).Ua (st (ℓ - 1)).Va D (st (ℓ - 1)).π).card : ℝ) := by sorry

end PCNonBool
