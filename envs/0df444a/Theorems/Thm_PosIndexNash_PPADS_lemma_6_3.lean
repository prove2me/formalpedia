-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_lemma_6_3
-- name    : PosIndexNash.PPADS.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:33:11.775425+00:00
-- url     : https://prove2.me/theorems/3b3a7ad1-5004-425c-95f2-d25c9c968e9e
-- title:
--   Lemma 6.3 — full imitation game correspondence: solutions of (42) ↔ all Nash equilibria of (S, I_N)
-- statement:
--   In the setting of §6 (an anchored normal form whose LCP solutions are strictly complementary and regular), let $x$ solve (42), $I = I(x) = \{i : x_i > 0\}$ and $K = I \cup \{\star\}$. Define
--   $$u_i := \begin{cases} 1/|K| & i \in K,\\ 0 & i\notin K,\end{cases}\qquad y := \frac{(x,1)}{1 + \mathbf 1^\top x}. \tag{50}$$
--   Then $(u, y)$ is a Nash equilibrium of the imitation game $G = (S, I_N)$. Moreover, every Nash equilibrium of $G$ is obtained in this way from exactly one solution $x$.
--
--   Differences from the source:
--   - generalization: "the LCP (42) built in §5 from the circuit of Theorem 4.2" → the LCP of any anchored normal form whose solutions are strictly complementary and regular; reason: the proof uses (43)–(44) and strict complementarity (48); the paper's LCP is one such, so the statement specializes.
--   - encoding: "obtained uniquely in this way" → for every equilibrium $(u, y)$ there is a unique solution $x$ with $u = u(x)$ and $y = y(x)$; strategy $\star$ is `Fin.last m`; reason: meaning of the sentence; Lean indexing.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 42, Lemma 6.3

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_IsNE
import Definitions.Def_PosIndexNash_PPADS_NormalForm
import Definitions.Def_PosIndexNash_PPADS_LCP
import Definitions.Def_PosIndexNash_PPADS_ImitationGame

open Matrix

namespace PosIndexNash.PPADS

theorem lemma_6_3 (F : NormalForm) (hF : F.Anchored)
    (hsc : ∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      ∀ i, 0 < x i + ((F.M.map ((↑) : ℚ → ℝ)) *ᵥ x - fun i => (F.b i : ℝ)) i)
    (hreg : ∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      ((F.M.map ((↑) : ℚ → ℝ)).submatrix
        (Subtype.val : {i // i ∈ QuasiStrictNE.supp x} → Fin F.m) Subtype.val).det ≠ 0) :
    (∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      QuasiStrictNE.IsNE ((symGameS F).map ((↑) : ℚ → ℝ)) (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ)
        (uOf x) (yOf x)) ∧
    (∀ u y : Fin (F.m + 1) → ℝ,
      QuasiStrictNE.IsNE ((symGameS F).map ((↑) : ℚ → ℝ)) (1 : Matrix (Fin (F.m + 1)) (Fin (F.m + 1)) ℝ)
        u y →
      ∃! x, x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))) ∧
        u = uOf x ∧ y = yOf x) := by sorry

end PosIndexNash.PPADS
