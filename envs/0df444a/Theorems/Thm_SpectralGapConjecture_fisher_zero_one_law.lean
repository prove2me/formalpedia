-- Prove2me | Theorems.Thm_SpectralGapConjecture_fisher_zero_one_law
-- name    : SpectralGapConjecture.fisher_zero_one_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T02:02:17.802172+00:00
-- url     : https://prove2.me/theorems/a17b51f5-f2c0-49ea-aa52-21fdff0aa924
-- title:
--   Fisher's zero–one law for the spectral gap
-- statement:
--   Let $\mu_2$ be the normalized Haar measure on $SU(2)$ and, for $g \in SU(2)^n$, let $z_g$ be the Hecke operator $(z_g f)(x) = \sum_{j=1}^{n}\bigl(f(g_jx) + f(g_j^{-1}x)\bigr)$.
--
--   For every $n \ge 3$, exactly one of the following alternatives holds (at least one, formally):
--
--   1. for $\mu_2^{\otimes n}$-almost every $g\in SU(2)^n$, $\lambda_1(z_g) < 2n$ (spectral gap);
--   2. for $\mu_2^{\otimes n}$-almost every $g\in SU(2)^n$, $\lambda_1(z_g) = 2n$ (no spectral gap).
--
--   Hence, to prove the spectral gap conjecture for $n\ge 3$ it suffices to find a set of $n$-tuples of positive Haar measure that all have a spectral gap.
--
--   **Formalization Note.** Alternative 2 is stated as "almost every tuple fails the spectral gap property", which is equivalent to $\lambda_1 = 2n$ since $\lambda_1 \le 2n$ always.
-- source:
--   D. Fisher, Out(F_n) and the spectral gap conjecture, IMRN 2006, arXiv:math/0601050, Theorem 1.2, p. 1

import Mathlib
import Definitions.Def_SpectralGapConjecture_HeckeSU

open MeasureTheory

namespace SpectralGapConjecture

theorem fisher_zero_one_law (n : ℕ) (hn : 3 ≤ n) :
    (∀ᵐ g ∂(Measure.pi fun _ : Fin n => haarSU 2), HasSpectralGap (haarSU 2) g) ∨
      (∀ᵐ g ∂(Measure.pi fun _ : Fin n => haarSU 2), ¬ HasSpectralGap (haarSU 2) g) := by sorry

end SpectralGapConjecture
