-- Prove2me | Theorems.Thm_PosIndexNash_PPADS_lemma_6_2
-- name    : PosIndexNash.PPADS.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:33:08.386558+00:00
-- url     : https://prove2.me/theorems/b1bbccc7-6c58-4881-ae2b-53c0143842ab
-- title:
--   Lemma 6.2 — LCP–symmetric equilibrium correspondence: solutions of (42) ↔ symmetric Nash equilibria of (S, Sᵀ)
-- statement:
--   Let $M, b$ be the LCP data of an anchored normal form (43)–(44), and assume (as §6 does, by Lemmas 5.4 and 5.5) that every solution of the LCP
--   $$x \ge 0,\qquad w := Mx - b \ge 0,\qquad x_i w_i = 0 \tag{42}$$
--   is strictly complementary ($x_i + w_i > 0$) and has $\det M_{I(x),I(x)} \ne 0$. Let $S = \begin{pmatrix}-M & b+\mathbf 1\\ \mathbf 0^\top & 1\end{pmatrix}$ (45). The solutions of (42) are in one-to-one correspondence with the symmetric Nash equilibria of $(S, S^\top)$: if $x$ solves (42), then with
--   $$y := \frac{(x, 1)}{1 + \mathbf 1^\top x} \tag{46}$$
--   $(y, y)$ is a symmetric Nash equilibrium; conversely, if $y = (\hat x, t)$ and $(y, y)$ is a symmetric Nash equilibrium, then $\hat x / t$ solves (42). In Lean the correspondence is stated by the two maps and the identities $y(\hat x/t) = y$ and $\widehat{y(x)}/t(y(x)) = x$.
--
--   Differences from the source:
--   - generalization: "the LCP (42) built in §5 from the circuit of Theorem 4.2" → the LCP of any anchored normal form whose solutions are strictly complementary and regular (the properties §6 takes from Lemmas 5.4–5.5); reason: the proof uses only (43)–(44); the paper's LCP is one such, so the statement specializes.
--   - encoding: "one to one correspondence" → the forward map, the backward map $y \mapsto \hat x/t$, and the two inverse identities; strategy $\star$ is the last index `Fin.last m`; reason: meaning of the correspondence; Lean indexing.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 41, Lemma 6.2

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_IsNE
import Definitions.Def_PosIndexNash_PPADS_NormalForm
import Definitions.Def_PosIndexNash_PPADS_LCP
import Definitions.Def_PosIndexNash_PPADS_ImitationGame

open Matrix

namespace PosIndexNash.PPADS

theorem lemma_6_2 (F : NormalForm) (hF : F.Anchored)
    (hsc : ∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      ∀ i, 0 < x i + ((F.M.map ((↑) : ℚ → ℝ)) *ᵥ x - fun i => (F.b i : ℝ)) i)
    (hreg : ∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      ((F.M.map ((↑) : ℚ → ℝ)).submatrix
        (Subtype.val : {i // i ∈ QuasiStrictNE.supp x} → Fin F.m) Subtype.val).det ≠ 0) :
    (∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      QuasiStrictNE.IsNE ((symGameS F).map ((↑) : ℚ → ℝ)) ((symGameS F).map ((↑) : ℚ → ℝ))ᵀ
        (yOf x) (yOf x)) ∧
    (∀ y : Fin (F.m + 1) → ℝ,
      QuasiStrictNE.IsNE ((symGameS F).map ((↑) : ℚ → ℝ)) ((symGameS F).map ((↑) : ℚ → ℝ))ᵀ
        y y →
      (fun i => y (Fin.castSucc i) / y (Fin.last F.m)) ∈
          LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))) ∧
        yOf (fun i => y (Fin.castSucc i) / y (Fin.last F.m)) = y) ∧
    (∀ x ∈ LCPSol (F.M.map ((↑) : ℚ → ℝ)) (-(fun i => (F.b i : ℝ))),
      (fun i => yOf x (Fin.castSucc i) / yOf x (Fin.last F.m)) = x) := by sorry

end PosIndexNash.PPADS
