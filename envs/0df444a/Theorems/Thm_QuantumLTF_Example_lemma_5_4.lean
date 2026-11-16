-- Prove2me | Theorems.Thm_QuantumLTF_Example_lemma_5_4
-- name    : QuantumLTF.Example.lemma_5_4
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T20:38:08.14477+00:00
-- url     : https://prove2.me/theorems/cbfe0e85-1811-474b-adfb-4cc5b42e3ab7
-- title:
--   Lemma 5.4 — Assouad’s lemma
-- statement:
--   Let $P_z$ be the output distribution of an estimator $\widehat z\in\{\pm1\}^m$ when the hidden string is $z$. If neighboring hidden strings induce output distributions of total-variation distance at most $\alpha$, then for uniform $z$,
--   $$\mathbb E[d_{\rm Ham}(z,\widehat z)]\ge \frac m2(1-\alpha).$$
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, STOC 2027 submission #347, Lemma 5.4, p. 75 (PDF p. 76).

import Mathlib
import Definitions.Def_QuantumLTF_Example_LowerModel

namespace QuantumLTF.Example

theorem lemma_5_4 :
    ∀ m : ℕ, 1 ≤ m → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      ∀ P : SignString m → PMF (SignString m),
        (∀ z i, pmfTV (P z) (P (Function.update z i (!(z i)))) ≤ α) →
        (1 / (2 : ℝ) ^ m) * ∑ z : SignString m, ∑ zh : SignString m,
          (P z zh).toReal * hamming z zh ≥ (m : ℝ) / 2 * (1 - α) := by sorry

end QuantumLTF.Example
