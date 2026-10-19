-- Prove2me | Theorems.Thm_SharingPlatform_WageSchemes_lemma_3
-- name    : SharingPlatform.WageSchemes.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:57.209983+00:00
-- url     : https://prove2.me/theorems/83540d20-9822-4211-a390-e23c175a5a61
-- title:
--   Lemma 3, p. 12 (PDF 13) — the FW subgame-perfect equilibrium: wage (8) and price (9)
-- statement:
--   Consider the fixed-wage game: in stage 1 the platforms announce wages $w_1, w_2 \in \mathbb R$, in stage 2 they set prices, and profit is $(p_i - w_i)\max\{0,\min\{d_i,s_i\}\}$. Assume the standing assumptions, including Assumption 2, $l \le 2c + c^2/b$. Let
--
--   $$w^* = \frac{b[2a(l+m) + 2ck + k(2l+3m)] + c[(a+2k)(l+m) + ck]}{b[2c(l+2m) + m(2l+3m)] + c[c(l+2m) + 2m(l+m)]}, \qquad p^* = \frac{a + k - m w^*}{c}.$$
--
--   Then:
--   1. there is a symmetric, non-trivial subgame-perfect equilibrium whose stage-2 price rules are continuous at $(w^*, w^*)$, in which both platforms announce $w^*$ and charge $p^*$;
--   2. every symmetric, non-trivial subgame-perfect equilibrium whose stage-2 price rules are continuous at the equilibrium pair has wage $w^*$ and on-path price $p^*$.
--
--   This is the FW outcome of Proposition 3. Assumption 2 is what makes the pure-strategy equilibrium exist (p. 9 and A.5).
--
--   **Formalization Note** "Non-trivial" means positive on-path demand and supply (p. 9). Continuity of the stage-2 price rules at the equilibrium pair is the same regularity condition as in Lemma 2, imposed on both two-stage games alike. The appendix's own argument differentiates the subgame prices (50) in the wages.
-- source:
--   Zhang, Chen, Raghunathan, Two-Sided Platform Competition in a Sharing Economy, SSRN 3555993, p. 12 (PDF 13), Lemma 3, Equations (8)–(9); proof A.5, pp. 43–46 (PDF 44–47)

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

namespace SharingPlatform.WageSchemes

theorem lemma_3 (P : Params) (hP : P.Standing) :
    (∃ e : TwoStage, IsSPE P fwWage e ∧ e.OnPathContinuous ∧ e.IsSymmetric ∧
      e.Nontrivial P fwWage ∧ e.x₁ = wW P ∧ e.P₁ e.x₁ e.x₂ = pW P) ∧
    (∀ e : TwoStage, IsSPE P fwWage e → e.OnPathContinuous → e.IsSymmetric →
      e.Nontrivial P fwWage → e.x₁ = wW P ∧ e.P₁ e.x₁ e.x₂ = pW P) := by sorry
end SharingPlatform.WageSchemes
