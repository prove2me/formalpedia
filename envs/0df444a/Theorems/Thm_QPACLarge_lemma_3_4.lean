-- Prove2me | Theorems.Thm_QPACLarge_lemma_3_4
-- name    : QPACLarge.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:10:43.819868+00:00
-- url     : https://prove2.me/theorems/0b8819ab-53c0-40f0-84bb-f673a1af3456
-- title:
--   Lemma 3.4 — under $P_F$, $\mathbb E[Y_x]=1/\sqrt N$, $\mathbb E[Y_xY_y]=1/N$, and $Y_x,Y_y$ are independent
-- statement:
--   Let $n \ge 1$, $N = 2^n$, $f : \{0,1\}^n \to \{0,1\}$ with $F = (-1)^f$, and let $a \sim P_F$ be drawn from the measurement law of the quantum sampler on the quadratic family. For $Y_x = F(x)H_a(x)$:
--
--   1. $\mathbb E_{P_F}[Y_x] = 1/\sqrt N$ for every $x$;
--   2. $\mathbb E_{P_F}[Y_xY_y] = 1/N$ for every $x \ne y$;
--   3. for $x \ne y$, $Y_x$ and $Y_y$ are independent under $P_F$: $P_F(Y_x = s, Y_y = t) = P_F(Y_x = s)\,P_F(Y_y = t)$ for all $s, t \in \{-1, 1\}$.
--
--   A single measured hypothesis therefore agrees with the target at each input with a small positive bias, independently across pairs of inputs; Theorem 3.6 amplifies this bias by majority.
--
--   Differences from the source: none.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.4, p.27

import Mathlib
import Definitions.Def_QPACLarge_PF

namespace QPACLarge

open QAlgorithms

/-- **Lemma 3.4 (Pointwise Bias and Independence).**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.4, p.27: "For `a ∼ P_F`, define `Yₓ ≜ F(x)H_a(x)`. The following statements hold:
• `E_{P_F}[Yₓ] = 1/√N` for every `x`. • `E_{P_F}[YₓY_y] = 1/N` for every `x ≠ y`. • For `x ≠ y`, the
random variables `Yₓ` and `Y_y` are independent under `P_F`."

Stated for the quadratic family of Lemma 3.1 ("We use the quadratic Boolean family from Lemma 3.1",
p.27), `N = 2ⁿ`, `F = (−1)^f`.

**Formalization Note.** Expectations under `P_F` are `Σₐ P_F(a)·(·)`. Independence of two
`±1`-valued variables is the factorization of `P_F(Yₓ = s, Y_y = t)` for all `s, t ∈ {±1}`
(written `sgn σ`, `sgn τ` for bits `σ, τ`). -/
theorem lemma_3_4 (n : ℕ) (hn : 1 ≤ n) (f : Qubits n → Bool) :
    (∀ x : Qubits n, ∑ a : Seed n, PF f a * (sgn (f x) * sgn (qa a x)) = (Real.sqrt (2 ^ n))⁻¹) ∧
    (∀ x y : Qubits n, x ≠ y →
      ∑ a : Seed n, PF f a * ((sgn (f x) * sgn (qa a x)) * (sgn (f y) * sgn (qa a y))) =
        ((2 : ℝ) ^ n)⁻¹) ∧
    (∀ x y : Qubits n, x ≠ y → ∀ σ τ : Bool,
      (open Classical in
        ∑ a : Seed n, if sgn (f x) * sgn (qa a x) = sgn σ ∧ sgn (f y) * sgn (qa a y) = sgn τ
          then PF f a else 0) =
      (open Classical in
        ∑ a : Seed n, if sgn (f x) * sgn (qa a x) = sgn σ then PF f a else 0) *
      (open Classical in
        ∑ a : Seed n, if sgn (f y) * sgn (qa a y) = sgn τ then PF f a else 0)) := by sorry

end QPACLarge
