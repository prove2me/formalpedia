-- Prove2me | Theorems.Thm_TopDownParity1043_Main_lemma_10
-- name    : TopDownParity1043.Main.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:19:24.688705+00:00
-- url     : https://prove2.me/theorems/4442c152-0912-4893-be58-73c51f485525
-- title:
--   Lemma 10 — improved light patterns
-- statement:
--   Let $V$ be finite, let $k\ge1$, and let $X$ be any probability law on $\{0,1\}^V$ with $D_\infty(X)\le k$. If $0\le r\le(512k)^{-1}$, then
--   $$\Pr_{R\subseteq_r V}\left[\left|\left\{z\in\{0,1\}^R:\Pr[X_R=z]\le2^{-|R|-2k-2}\right\}\right|\le2^{|R|-k}\right]\ge\frac{63}{64}.$$
--
--   Here $X_R$ is the actual projected probability law and $k$ is real. Every threshold is inclusive. This is a statement about all probability laws, including laws that are not uniform on a set; it supplies the projection estimate behind the final depth lower bound.
--
--   Differences from the source:
--   - encoding: coordinates [n] → an arbitrary finite type V with Boolean words V → Bool; reason: every finite coordinate set is equivalent to Fin |V|, including every subcube coordinate subtype
--   - encoding: a real bias constrained by 0 ≤ r ≤ the stated upper bound → a bias in [0,1] with the same sharper upper bound; reason: the printed upper bound already implies r ≤ 1, so the subtype excludes no source instance
-- source:
--   Oliver Korten, STOC 2027 submission #1043 (October 2026), Lemma 10, p. 15

import Mathlib
import Definitions.Def_TopDownParity1043_Main_RandomSets
import Definitions.Def_TopDownParity1043_Main_Subcubes

set_option autoImplicit false
open scoped NNReal ENNReal

namespace TopDownParity1043.Main

/-- Lemma 10 (Improved Light Patterns), p.15. X is an arbitrary PMF, not just
a uniform-set law; every numerical threshold and inequality is inclusive as printed. -/
theorem lemma_10 (V : Type) [Fintype V] [DecidableEq V]
    (k : ℝ) (hk : 1 ≤ k) (r : Bias) (hr : (r : ℝ) ≤ (512 * k)⁻¹)
    (X : PMF (V → Bool)) (hX : lawDeficit X ≤ k) :
    (63 : ℝ) / 64 ≤ setProb r (fun R : Finset V =>
      (lightCount X R k : ℝ) ≤ (2 : ℝ) ^ ((R.card : ℝ) - k)) := by sorry

end TopDownParity1043.Main
