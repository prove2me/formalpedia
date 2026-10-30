-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P07_successOrDraw_repetition
-- name    : QAlgorithms.Papers.Independent.Extend50.P07.successOrDraw_repetition
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:50:00.860627+00:00
-- url     : https://prove2.me/theorems/93060a76-ea79-48e3-9ee4-f452f5743822
-- title:
--   Conditional amplification of a supplied success-or-draw protocol
-- statement:
--   Let $1\le d\le D$ be positive integer dimensions with fixed computational bases. Write $\mathcal E_V(X)=VXV^\dagger$ for an unknown isometry $V:\mathbb C^d\to\mathbb C^D$, where $V^\dagger V=I_d$. A protocol, including its finite memory and all its operations, is fixed before $V$. Its $k$ oracle slots receive the same channel $\mathcal E_V$, and every map identity below holds on every input operator. The uniform coefficient $p\in[0,1]$ is the scale in Eq. (5); the physical outcome probability on a density matrix $\rho$ is $p\operatorname{Tr}(f(V)(\rho))$.
--
--   Supply a physical $k$-slot success-or-draw protocol $A$ with coefficient $p\in[0,1]$. Let $W:\mathbb C^d\to\mathbb C^D$ be the fixed natural embedding. Its successful and draw branches obey
--
--   $$S_V(\mathcal E_V(X))=p\mathcal E_W(X),\qquad F_V(\mathcal E_V(X))=(1-p)\mathcal E_V(X).$$
--
--   The finite protocol tree that repeats $A$ after a draw, stopping at success or after $m$ rounds, has worst-case query count $mk$. Its successful and all-draw branches on a code input are respectively
--
--   $$[1-(1-p)^m]\mathcal E_W(X),\qquad (1-p)^m\mathcal E_V(X).$$
--
--   For $0<p<1$ there is a constant $C>0$, depending on the supplied protocol and $p$ but not on $\delta$, such that for every $0<\delta<1$ some $m$ achieves failure at most $\delta$ with query count at most $k+C\log(1/\delta)$. The exact formulas include $m=0$ and $p=1$; one round suffices when $p=1$. This is conditional and does not assert exact feasibility of the numerically reported instance.
-- source:
--   Universal construction of decoders from encoding black boxes, arXiv:2110.00258v5, PDF p. 24, §5: amplification by repeating a success-or-draw protocol

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P07

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P06 (Choi)

open QAlgorithms.Papers.Independent.Information100.P34 (choi fromChoi)

open QAlgorithms.Papers.Independent.Claimed50.P48 (FiniteKrausCP)

open QAlgorithms.Papers.Independent.Advance50.P05 (RectangularInstrument)

open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

/-- arXiv:2110.00258v5 PDF pp.23--24,43: conditional amplification of a
supplied physical success-or-draw protocol. The output uses the fixed embedding
of Eq. (38). At p=1 the one-round formula applies without a logarithmic denominator.
Eq. (211)'s printed p is corrected to 1-p, as in Eqs. (69),(213),(218). -/
theorem successOrDraw_repetition (d D k : ℕ) (hd : 0 < d) (hD : d ≤ D)
    (A : General d D D D k) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hS : ∀ V : Isometry d D, ∀ X,
      A.run V (conjSuperop V.val X) = (p : ℂ) • conjSuperop (embedding d D) X)
    (hF : ∀ V : Isometry d D, ∀ X,
      A.draw V (conjSuperop V.val X) = ((1 - p : ℝ) : ℂ) • conjSuperop V.val X) :
    (∀ m : ℕ, (repeatProtocol A m).queryCount = m * k ∧
      ∀ V : Isometry d D, ∀ X,
      (repeatProtocol A m).success V (conjSuperop V.val X) =
        ((1 - (1 - p)^m : ℝ) : ℂ) • conjSuperop (embedding d D) X ∧
      (repeatProtocol A m).failure V (conjSuperop V.val X) =
        (((1 - p)^m : ℝ) : ℂ) • conjSuperop V.val X) ∧
    (0 < p → p < 1 → ∃ C : ℝ, 0 < C ∧ ∀ delta : ℝ,
      0 < delta → delta < 1 → ∃ m : ℕ,
        (1 - p)^m ≤ delta ∧
        ((repeatProtocol A m).queryCount : ℝ) ≤ (k : ℝ) + C * Real.log (1 / delta)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P07

end
