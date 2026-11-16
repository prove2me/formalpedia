-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_Supplement_lemma_6_6
-- name    : ParityBarrier563.Trilinear.Supplement.lemma_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:51:50.080873+00:00
-- url     : https://prove2.me/theorems/b14f71a5-22db-40dd-85b6-aa1f0236f22c
-- title:
--   Lemma 6.6 — Averaged slice correlation after fixing data and seed coordinates
-- statement:
--   Let $n\ge1$, integers $k\ge b\ge1$, $0<q\le1$, $p=b/(64k)$, $\eta=qp$ and $m=\eta n$. Let u be even with $u\ge512$, $u\le m/4$, $u\eta\le1/4$, $m\ge512u\ln(n+1)$. Suppose an integer $1\le L\le u/512$ gives a decomposition of every b-CNF on every set of $t\le4m$ variables into at most $2^{t/128}$ closures with point lists of size at most L. Put $R=\lfloor m/128\rfloor$. For every restriction τ fixing at most R of all $4n-1$ trilinear input coordinates,
--   $$\mathbb E_{a\mid\tau}\mathbb E_\varphi\operatorname{corr}_k((g^a)_{\tau\varphi})\le8e^{-m/512}.$$
--   The remaining seed bits are uniform extensions of the seed part of τ; φ independently q-restricts only remaining data bits. Only the data part of τ acts on $g^a=2f_n^a-1$. This is the averaged slice estimate with arbitrary fixed seed and data values.
--
--   Differences from the source:
--   - encoding: every finite variable set and conditioned seed extensions → Fin t representatives and a finite uniform cube of live seed bits; reason: the representations are equivalent and compatible seeds are always nonempty
--   - encoding: R is the integer floor of m/128 → the natural floor of m/128; reason: m is positive under the printed numerical hypotheses, so the two floors agree
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), Lemma 6.6, printed p.28 / PDF p.30

import Definitions.Def_ParityBarrier563_Trilinear_Supplement_SeedAndSubset

set_option autoImplicit false
open scoped Classical

namespace ParityBarrier563.Trilinear.Supplement

/-- Lemma 6.6: conditioning seed bits and restricting data bits are separate operations. -/
theorem lemma_6_6 (n k b : ℕ) (hb : 1 ≤ b) (hbk : b ≤ k)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) (u L : ℕ) (he : Even u)
    (hu : 512 ≤ u) (hL : 1 ≤ L) :
  let p := (b : ℝ)/(64*k)
  let η := q*p
  let m := η*n
  (u : ℝ) ≤ m/4 → (u : ℝ)*η ≤ 1/4 → m ≥ 512*u*Real.log (n+1) →
  (L : ℝ) ≤ (u : ℝ)/512 →
  (∀ t : ℕ, (t : ℝ) ≤ 4*m →
    HasClosureDecomp b (Fin t) ((2 : ℝ)^((t : ℝ)/128)) L) →
  ∀ τ : Restriction (TriVar n), fixedCount τ ≤ ⌊m/128⌋₊ →
    seedCorrelation τ q k ≤ 8*Real.exp (-m/512) := by sorry

end ParityBarrier563.Trilinear.Supplement
