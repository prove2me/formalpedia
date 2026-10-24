-- Prove2me | Theorems.Thm_UniversalBarrier_NSC_lemma_4
-- name    : UniversalBarrier.NSC.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:45.878066+00:00
-- url     : https://prove2.me/theorems/86fccbea-f6ac-4cbb-a7e1-7437a84ff75d
-- title:
--   Lemma 4, p. 17 — g(γ, k) ≥ 0 for every γ ≥ 1 and integer k ≥ 2
-- statement:
--   For every real $\gamma\ge1$ and every integer $k\ge2$,
--   $$g(\gamma,k)=4(k-1)^2\bigl((k+1)^2(\gamma^k-1)(\gamma^{k+2}-1)-k(k+2)(\gamma^{k+1}-1)^2\bigr)^3-\bigl(2k^2(k+2)(k+3)(\gamma^{k+1}-1)^3+(k+2)(k+1)^3(\gamma^k-1)^2(\gamma^{k+3}-1)-3k(k+3)(k+1)^2(\gamma^k-1)(\gamma^{k+1}-1)(\gamma^{k+2}-1)\bigr)^2\ \ge\ 0.$$
--
--   This polynomial inequality, (35) of the paper, is the last step of the proof of inequality (4): it is the bound $\Xi\le2\sqrt{(k+2)/k}\,(k-1)/(k+3)$ for the density proportional to $t^{k-1}$ on $[1,\gamma]$, cleared of denominators.
-- source:
--   Lee & Yue, Universal Barrier is n-Self-Concordant, arXiv:1809.03011v4, p. 17, Lemma 4 and (35)

import Mathlib
import Definitions.Def_UniversalBarrier_NSC_Model

namespace UniversalBarrier.NSC

theorem lemma_4 (k : ℕ) (hk : 2 ≤ k) (γ : ℝ) (hγ : 1 ≤ γ) : 0 ≤ gpoly k γ := by sorry

end UniversalBarrier.NSC
