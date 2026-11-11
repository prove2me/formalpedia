-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_lemma_6_5
-- name    : PosIndexNash.PPADS.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:33:32.086034+00:00
-- url     : https://prove2.me/theorems/a2ef53ab-16d6-49f8-9b17-1fccb8a292a6
-- title:
--   Lemma 6.5 — exact index identity: the imitation-game equilibrium of an LCP solution is regular, quasi-strict and has index sign det M_II
-- statement:
--   In the setting of §6 (an anchored normal form whose LCP solutions are strictly complementary and regular), let $x$ solve (42), set $I = I(x)$, and let $(u(x), y(x))$ be its equilibrium (50) in the imitation game $(S, I_N)$. Then this equilibrium is regular and quasi-strict ($\mathrm{supp}\,u = BR_1(y)$, $\mathrm{supp}\,y = BR_2(u)$), and
--   $$\mathrm{ind}\big(u(x), y(x)\big) = \mathrm{sign}\det M_{I,I}. \tag{52}$$
--   Together with Lemma 5.5 this gives $\mathrm{ind}(u(x), y(x)) = \mathrm{ind}_\Phi(\lambda)$: the passage from the signed Linear-FIXP instance to the imitation game preserves the sign.
--
--   Differences from the source:
--   - generalization: "the LCP (42) built in §5 from the circuit of Theorem 4.2" → the LCP of any anchored normal form whose solutions are strictly complementary and regular; reason: the proof uses (43)–(44), strict complementarity and $\det M_{II}\ne 0$; the paper's LCP is one such, so the statement specializes.
--   - encoding: the index with $K$ ordered "with $\star$ last" → `shapleyIndex` with supports in increasing order of `Fin (m+1)`, where $\star$ = `Fin.last m` is last; quasi-strictness is the public `QuasiStrictNE.IsQSNE`; reason: same ordering; same definition (p. 42).
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 43, Lemma 6.5

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_IsQSNE
import Definitions.Def_PosIndexNash_PPADS_NormalForm
import Definitions.Def_PosIndexNash_PPADS_LCP
import Definitions.Def_PosIndexNash_PPADS_ImitationGame
import Definitions.Def_PosIndexNash_PPADS_ShapleyIndex
import Definitions.Def_PosIndexNash_PPADS_IsRegularEq

open Matrix

namespace PosIndexNash.PPADS

theorem lemma_6_5 (F : NormalForm) (hF : F.Anchored)
    (hsc : ∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      ∀ i, 0 < x i + ((F.M.map ((↑) : ℚ → ℝ)) *ᵥ x - fun i => (F.b i : ℝ)) i)
    (hreg : ∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      ((F.M.map ((↑) : ℚ → ℝ)).submatrix
        (Subtype.val : {i // i ∈ QuasiStrictNE.supp x} → Fin F.m) Subtype.val).det ≠ 0) :
    ∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      QuasiStrictNE.IsQSNE ((symGameS F).map ((↑) : ℚ → ℝ))
          (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ) (uOf x) (yOf x) ∧
        IsRegularEq ((symGameS F).map ((↑) : ℚ → ℝ))
          (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ) (uOf x) (yOf x) ∧
        shapleyIndex ((symGameS F).map ((↑) : ℚ → ℝ))
            (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ) (uOf x) (yOf x) =
          ((SignType.sign ((F.M.map ((↑) : ℚ → ℝ)).submatrix
            (Subtype.val : {i // i ∈ QuasiStrictNE.supp x} → Fin F.m) Subtype.val).det :
              SignType) : ℤ) := by sorry

end PosIndexNash.PPADS
