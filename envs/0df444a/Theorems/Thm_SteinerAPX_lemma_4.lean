-- Prove2me | Theorems.Thm_SteinerAPX_lemma_4
-- name    : SteinerAPX.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:34:05.538319+00:00
-- url     : https://prove2.me/theorems/bde5c68a-f945-478f-91dc-a0e1f2d3a02e
-- title:
--   Lemma 4 (first sentence) — distinguishing $\nu(H)=r$ from $\nu(H)\le(1-\delta)r$ is NP-hard for 3DM-3
-- statement:
--   There is a constant $\delta>0$ such that the following promise problem is NP-hard: given an instance $H=(U,E)$ of 3DM-3 with parts of size $r$, decide whether
--   $$
--   \nu(H)=r\qquad\text{or}\qquad \nu(H)\le(1-\delta)\,r .
--   $$
--   Concretely, there is one $\delta\in(0,1)$ such that every language $\mathcal L$ in NP has a polynomial-time reduction mapping each word $x$ to a valid 3DM-3 instance $H_x$ with $r\ge1$, such that $x\in\mathcal L$ implies $\nu(H_x)=r$ and $x\notin\mathcal L$ implies $\nu(H_x)\le(1-\delta)r$.
--
--   This gap version of three-dimensional matching is the source problem of every reduction in the paper.
--
--   Differences from the source:
--   - encoding: NP-hard to distinguish the two cases → every language in NP (published CookLevin.InNP) reduces by a polynomial-time finite-alphabet TM2 machine to instances in the two cases; reason: the Karp-reduction meaning of NP-hardness of a promise problem, with the published machine model of PEqualsNP
--   - encoding: δ > 0 → 0 < δ < 1; reason: the soundness clause only gets stronger as δ grows, so a witness δ ≥ 1 yields the witness 1/2
--   - encoding: instances H of 3DM-3 → valid 3DM-3 instances with r ≥ 1; reason: at r = 0 the two cases coincide (ν = 0 = r), so the empty instance carries no gap
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 4, first sentence, p.4 (PDF p.6); proof Appendix A.3, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_SteinerAPX_Inst3DM

namespace SteinerAPX

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- **Lemma 4, first sentence (gap three-dimensional matching).** S. Bartlmae, *Inapproximability
of Euclidean Steiner Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), Lemma 4, p.4 (PDF
p.6): "For some constant δ > 0, distinguishing ν(H) = r from ν(H) ≤ (1 − δ)r is NP-hard for
instances H of 3DM-3." (Proof: Appendix A.3, p.38.)

**Formalization Note** NP-hardness of the promise problem: there is one `δ ∈ (0, 1)` such that
every language `L` in NP (`CookLevin.InNP`, the published verifier definition that `PEqualsNP`
uses) has a polynomial-time map (Mathlib `TM2ComputableInPolyTime`, finite alphabet) from words to
raw 3DM codes whose output is always a valid 3DM-3 instance with `r ≥ 1`, with `ν(H) = r` when
`x ∈ L` and `ν(H) ≤ (1 − δ)r` when `x ∉ L`. `δ < 1` loses nothing, since the soundness clause only
gets stronger as `δ` grows. Clauses (i)–(iii) of Lemma 4 (conditional on Gap-ETH, weak ETH,
NP ⊄ SUBEXP) are not part of this statement. -/
theorem lemma_4 :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ L : BitLanguage, CookLevin.InNP L →
    ∃ construct : List Bool → Raw3DM,
    ∃ comp : Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) Raw3DM.bits construct,
      MachineFiniteAlphabet.FiniteAlphabet comp.tm ∧
      ∀ x : List Bool, ∃ hR : (construct x).Valid,
        ((construct x).toInst hR).IsThreeDM3 ∧
        (L x → ((construct x).toInst hR).nu = ((construct x).toInst hR).r) ∧
        (¬ L x → ((((construct x).toInst hR).nu : ℕ) : ℝ) ≤
          (1 - δ) * (((construct x).toInst hR).r : ℝ)) := by sorry

end SteinerAPX
