-- Prove2me | Theorems.Thm_RegevRecon_channel_fourier_ne_zero
-- name    : RegevRecon.channel_fourier_ne_zero
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:20.269215+00:00
-- url     : https://prove2.me/theorems/d03d4c58-413e-4854-bd05-a483731c6d9f
-- title:
--   $\hat\mu(b)\ne0$ for $\beta>0$, $b\ne0$
-- statement:
--   For $\beta>0$ and $b\ne0$ in $\mathbb F_p$, the Fourier coefficient $\hat\mu(b)$ of the physical channel is a positive multiple of $\sum_{a\in S}\omega^{ab}$, and this sum does not vanish for a prime $p$ and a nonempty proper $S$. Hence $\hat\mu(b)\ne0$. This uses the primality of $p$: the minimal polynomial of $\omega^b$ is $1+X+\dots+X^{p-1}$.
--
--   Differences from the source: none.
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), p.24

import Mathlib
import Definitions.Def_RegevRecon_Messages

namespace RegevRecon

/-- **Nonvanishing of `μ̂(b)`**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), p.24: "For β > 0, each μ̂(b), b ≠ 0, is nonzero: it is a positive
multiple of Σ_{a∈S} ω^{ab}, which cannot vanish for prime p and a nonempty proper S."  -/
theorem channel_fourier_ne_zero {p : ℕ} [Fact p.Prime] (S : Finset (ZMod p)) (hS : S.Nonempty)
    (hS' : S ≠ Finset.univ) (β : ℝ) (hβ : 0 < β) (b : ZMod p) (hb : b ≠ 0) :
    (∃ c : ℝ, 0 < c ∧ fourier (channel S β) b = (c : ℂ) * ∑ a ∈ S, zeta (a * b)) ∧
      ∑ a ∈ S, zeta (a * b) ≠ 0 ∧ fourier (channel S β) b ≠ 0 := by sorry

end RegevRecon
