-- Prove2me | Theorems.Thm_RegevLWE_Correctness_rounding
-- name    : RegevLWE.Correctness.rounding
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:07:37.937192+00:00
-- url     : https://prove2.me/theorems/05aea60a-3f12-4bf7-9e5b-3468f4615b42
-- title:
--   Proof of Lemma 5.1, p. 34:36 — |x| < ⌊p/2⌋/2 implies x is closer to 0 than to ⌊p/2⌋, so decryption is correct
-- statement:
--   Let $p \ge 2$ and, for $a \in \mathbb Z_p$, let $|a|$ be its distance from $0$ modulo $p$ (the integer $a$ if $a \le \lfloor p/2\rfloor$, else $p - a$). Let $x \in \mathbb Z_p$ satisfy
--   $$|x| < \Bigl\lfloor \frac p2 \Bigr\rfloor \Big/ 2 .$$
--   Then:
--   1. $x$ is closer to $0$ than to $\lfloor p/2\rfloor$ modulo $p$: $|x| < |x - \lfloor p/2\rfloor|$;
--   2. the residue $x$ decrypts to $0$;
--   3. the residue $\lfloor p/2\rfloor + x$ decrypts to $1$.
--
--   Items 2 and 3 say that, when the accumulated noise is small, the decryption of an encryption of either bit is correct.
--
--   **Formalization Note** $\lfloor p/2\rfloor/2$ may be a half-integer, so the hypothesis compares $|x|$ with it in $\mathbb R$. "Decrypts to" refers to the decision rule `decodeResidue` applied to the residue $b - \langle a, s\rangle$. Item 3 is the bit-1 case the page calls "similar".
-- source:
--   Regev, On Lattices, Learning with Errors, Random Linear Codes, and Cryptography, J. ACM 56(6) (2009), Article 34, p. 34:36, proof of Lemma 5.1 ("In this case, it is closer to 0 than to ⌊p/2⌋ and therefore the decryption is correct.")

import Mathlib
import Definitions.Def_RegevLWE_Correctness_Cryptosystem

open Matrix

namespace RegevLWE.Correctness

/-- Proof of Lemma 5.1 (Regev, J. ACM 2009, p. 34:36): let `p ≥ 2` and `x ∈ ℤ_p` with
`|x| < ⌊p/2⌋/2` (the bound compared in `ℝ`). Then `x` is closer to `0` than to `⌊p/2⌋`
modulo `p`, so the residue `x` decrypts to `0`, and the residue `⌊p/2⌋ + x` (an encryption
of `1`) decrypts to `1`. -/
theorem rounding {p : ℕ} [NeZero p] (hp : 2 ≤ p) (x : ZMod p)
    (hx : (absZ x : ℝ) < ((p / 2 : ℕ) : ℝ) / 2) :
    absZ x < absZ (x - ((p / 2 : ℕ) : ZMod p)) ∧
      decodeResidue x = 0 ∧
      decodeResidue (((p / 2 : ℕ) : ZMod p) + x) = 1 := by sorry

end RegevLWE.Correctness
