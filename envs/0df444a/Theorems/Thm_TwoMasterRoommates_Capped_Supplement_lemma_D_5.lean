-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_Supplement_lemma_D_5
-- name    : TwoMasterRoommates.Capped.Supplement.lemma_D_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:36:39.888929+00:00
-- url     : https://prove2.me/theorems/2986dccf-0fcf-4755-ac3a-5c7b8610cf9c
-- title:
--   Lemma D.5 — exact affine compiler from bounded-occurrence formulas
-- statement:
--   Let $\varphi$ have $n\ge1$ variables and $m$ labelled clauses of size at most three, with at most five literal occurrences of each variable, and let $u^*$ be its minimum number of unsatisfied clauses. There are polynomial-time computable maps, a compiler and a decoder, such that for every such $\varphi$ the compiler outputs an instance of the preference domain of Theorem D.1 on
--
--   $$N=28n+2m$$
--
--   agents, with rewards in $\{0,21,22,23,31\}$, and with $K=321n+22m$:
--
--   1. $\mathrm{OPT}=K-u^*$: some weakly stable perfect matching has reward $K-u^*$ and none has more;
--   2. for every weakly stable perfect matching $M$ of reward $R$, the decoder applied to $(\varphi,M)$ returns an assignment with at most $K-R$ unsatisfied clauses;
--   3. for every assignment with $u$ unsatisfied clauses there is a weakly stable perfect matching of reward $K-u$.
--
--   The deficit $K-w(M)$ of a stable matching thus controls the number of unsatisfied clauses exactly, which transfers a MAX-SAT gap to maximum-reward stable matching in Theorem D.6.
--
--   Differences from the source:
--   - encoding: construct in polynomial time; decodes in polynomial time → PolyTimeComputable maps on binary codes: the compiler on the code of φ, the decoder on the code of φ followed by the code of M; reason: the published Cook framework's notion of polynomial-time computation
--   - encoding: OPT = K − u* → a weakly stable perfect matching of reward K − u* exists and every weakly stable perfect matching has reward at most K − u*; reason: this is the equality for the maximum over a finite nonempty set without a junk value
--   - encoding: weakly stable matching → weakly stable perfect matching (IsSolution with all caps ⊤); reason: N = 28n + 2m is even and §C/§3 note that weakly stable matchings of even complete instances are perfect
--   - encoding: a formula with labelled clauses → variables Fin n and a list of clauses, each a list of (sign, variable) literals; labels are list positions, occurrences are literal positions; reason: the lemma's input class, with no extra condition on clauses
--   - encoding: every A observer indifferent among all other agents, every B observer following one whole strict master b with all A identities first, no caps → an Instance ℤ n with every cap ⊤, the master a constant on all identities (own entries included), and b injective with b(x) < b(y) for x ∈ A, y ∈ B; reason: an observer's own entry is never compared (Blocks requires u ≠ v and a perfect matching has no fixed point), and integer ranks represent every flat or strict order on a finite set
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 25 (PDF p. 26), Lemma D.5

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Supplement_Hardness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped.Supplement

open TwoMasterRoommates.Capped

/-- Lemma D.5 (exact affine compiler), Bin Yu, STOC 2027 submission #225, p. 25 (PDF 26). -/
theorem lemma_D_5 :
    ∃ compile decode : List Bool → List Bool,
      CookPvsNP.PolyTimeComputable compile ∧ CookPvsNP.PolyTimeComputable decode ∧
      ∀ φ : Formula, φ.Valid5 →
        ∃ (I : Instance ℤ φ.agents) (w : Sym2 (Fin φ.agents) → ℤ),
          compile φ.enc = encI I w ∧ FlatStrict I ∧ setRule alphabetD6 φ.agents I w ∧
          ((∃ M, IsSolution I M ∧ edgeSum w M = φ.K - (φ.ustar : ℤ)) ∧
            ∀ M, IsSolution I M → edgeSum w M ≤ φ.K - (φ.ustar : ℤ)) ∧
          (∀ M, IsSolution I M → ∃ τ : Fin φ.n → Bool,
            decode (φ.enc ++ encM M) = φ.encA τ ∧ (φ.unsat τ : ℤ) ≤ φ.K - edgeSum w M) ∧
          ∀ τ : Fin φ.n → Bool, ∃ M, IsSolution I M ∧ edgeSum w M = φ.K - (φ.unsat τ : ℤ) := by sorry

end TwoMasterRoommates.Capped.Supplement
