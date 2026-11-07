-- Prove2me | Theorems.Thm_SigmoidWire_parity_sign_degree
-- name    : SigmoidWire.parity_sign_degree
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:23.802949+00:00
-- url     : https://prove2.me/theorems/9de18820-d425-48bc-af28-9195a6d7559d
-- title:
--   [PS94, Lemma 3] as used in the proof of Corollary 4.6: the sign-degree of parity
-- statement:
--   Let $\oplus_n$ be parity on $n$ bits.
--
--   1. If a real multivariate polynomial $p$ satisfies $\oplus_n(x)=\mathrm{sgn}(p(x))$ for every $x\in\{0,1\}^n$, then $\deg p\ge n$.
--   2. If a rational function of degree at most $D$ sign-represents $\oplus_n$, then $D\ge n/2$.
--
--   Here $\mathrm{sgn}(t)=1$ iff $t>0$, so $p$ may vanish on even-weight inputs. This is the lower bound that Theorem 4.4 is played against.
--
--   Differences from the source:
--   - reading: "the polynomial P · Q also sign-represents Parity" → sgn with the paper's convention: p > 0 on odd inputs and p ≤ 0, possibly 0, on even inputs; reason: this is what sgn (p.14) gives for P · Q, and the form the proof needs; it is more demanding than p < 0 on even inputs
-- source:
--   Li, Reichman, Williams, Wu, New Gate, Weight and Wire Complexity Bounds for Sigmoid Neural Networks, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Corollary 4.6, p.20, citing [PS94, Lemma 3] and [PS94, Corollary 1]

import Mathlib
import Definitions.Def_SigmoidWire_bitR
import Definitions.Def_SigmoidWire_SignRepBy
import Definitions.Def_GeoQAC_parityFn

namespace SigmoidWire

/-- **[PS94, Lemma 3] as used in the proof of Corollary 4.6: parity has sign-degree `n`, and
rational sign-degree at least `n/2`.**

J. Li, D. Reichman, R. Williams, T. Wu, *New Gate, Weight and Wire Complexity Bounds for Sigmoid
Neural Networks*, STOC 2027 submission (manuscript sha256 2d6ef7af…), proof of Corollary 4.6, p.20
(PDF p.22): "suppose that a rational function P/Q sign-represents Parity, where Q has no zero on
{0, 1}^n. Then the polynomial P · Q also sign-represents Parity, so deg P + deg Q ≥ n by
[PS94, Lemma 3] (see also [PS94, Corollary 1]). Hence the degree of P/Q is at least n/2".

**Formalization Note.** Parity is the published `GeoQAC.parityFn n` ("the number of ones of `x` is
odd"). The first conjunct is [PS94, Lemma 3] in the form the proof uses: a real polynomial `p` with
`Parity(x) = sgn(p(x))` on `{0,1}^n` (with the paper's `sgn`, `p ≤ 0`, possibly `= 0`, on even
inputs) has total degree at least `n`. The second is the conclusion "the degree of `P/Q` is at least
`n/2`" for every rational sign-representation (`SignRepBy`). -/
theorem parity_sign_degree :
    (∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ),
      (∀ x : Fin n → Bool, GeoQAC.parityFn n x = true ↔ 0 < MvPolynomial.eval (cubePt x) p) →
        n ≤ p.totalDegree) ∧
    ∀ (n : ℕ) (D : ℝ), SignRepBy (GeoQAC.parityFn n) D → (n : ℝ) / 2 ≤ D := by sorry

end SigmoidWire
