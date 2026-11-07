-- Prove2me | Theorems.Thm_QCopyMono_eq_5_6
-- name    : QCopyMono.eq_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:44:37.076297+00:00
-- url     : https://prove2.me/theorems/32cf825b-007f-4b7b-b713-ce599dbb1e2c
-- title:
--   Eqs. (5)–(6) — laws, means and second moments of the Fourier-tester estimators $Y$ and $Z$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ with sign representation $g$.
--
--   1. Apply $H^{\otimes(n+1)}$ to $|\psi_f\rangle$ and measure in the computational basis. The last qubit is $1$ with probability $1/2$, and the outcome $(S,1)$ has probability $\hat g(S)^2/2$.
--   2. For $Y=2|S|$ on last qubit $1$ and $Y=0$ otherwise,
--   $$
--   \mathbb E[Y]=I[g],\qquad \mathrm{Var}(Y)\le\mathbb E[Y^2]=2\sum_{S\subseteq[n]}|S|^2\hat g(S)^2\le 2nI[g].
--   $$
--   3. Measuring $|\psi_f\rangle$ in the computational basis gives a uniformly random labeled example $(x,f(x))$: outcome $(x,c)$ has probability $2^{-n}$ if $c=f(x)$ and $0$ otherwise. For $Z=g(z)\sum_{i}z_i$,
--   $$
--   \mathbb E[Z]=\sum_{i=1}^n\hat g(\{i\}),\qquad \mathrm{Var}(Z)\le\mathbb E[Z^2]=n.
--   $$
--   These are the variance bounds that, after the influence filter, give the Fourier tester its $n^{3/2}/\varepsilon^2$ copy count.
--
--   Differences from the source:
--   - encoding: E, Var of the measurement outcomes Y and Z → finite sums against the outcome probability mass functions; Var(W) = Σ P(ω)(W(ω) − E[W])²; reason: the outcome sets are finite; same quantities
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), proof of Proposition 1, pp.7–8, eqs. (5) and (6)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_Influence
import Definitions.Def_QCopyMono_FourierSampling

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), proof of Proposition 1, pp.7–8, eqs. (5)–(6):
the two one-copy estimators of the Fourier tester, from their actual outcome laws.

1. Fourier sampling (apply `H^{⊗(n+1)}`, measure in the computational basis): the last qubit is
   `1` with probability `1/2`, and the outcome `(S, 1)` has probability `ĝ(S)²/2`.
2. `Y = 2|S|` on last qubit `1`, else `0`: `E[Y] = I[g]`, `Var(Y) ≤ E[Y²]`,
   `E[Y²] = 2 ∑_S |S|² ĝ(S)²`, and `2 ∑_S |S|² ĝ(S)² ≤ 2n I[g]` (eq. (5)).
3. Computational-basis measurement gives a uniformly random labeled example `(x, f(x))`, and
   `Z = g(z) ∑ᵢ zᵢ` has `E[Z] = ∑ᵢ ĝ({i})`, `Var(Z) ≤ E[Z²]`, `E[Z²] = n` (eq. (6)).

**Formalization Note.** Expectations are finite sums against the outcome probabilities
`fourierProb f` and `compProb f`; `Var(W)` is `∑ P(ω)(W(ω) − E[W])²`. A subset `S ⊆ [n]` is a
measured bit string `s` with `S = outSet s`. -/
theorem eq_5_6 (n : ℕ) (f : Qubits n → Bool) :
    (∀ s : Qubits n, fourierProb f (s, true) = fourierCoeff f (outSet s) ^ 2 / 2) ∧
    (∑ s : Qubits n, fourierProb f (s, true) = 1 / 2) ∧
    (∑ a : X n, fourierProb f a * fourierY a = influence f) ∧
    (∑ a : X n, fourierProb f a * (fourierY a - influence f) ^ 2 ≤
      ∑ a : X n, fourierProb f a * fourierY a ^ 2) ∧
    (∑ a : X n, fourierProb f a * fourierY a ^ 2 =
      2 * ∑ S : Finset (Fin n), (S.card : ℝ) ^ 2 * fourierCoeff f S ^ 2) ∧
    (2 * ∑ S : Finset (Fin n), (S.card : ℝ) ^ 2 * fourierCoeff f S ^ 2 ≤ 2 * n * influence f) ∧
    (∀ a : X n, compProb f a = if a.2 = f a.1 then 1 / 2 ^ n else 0) ∧
    (∑ a : X n, compProb f a * estZ a = ∑ i : Fin n, fourierCoeff f {i}) ∧
    (∑ a : X n, compProb f a * (estZ a - ∑ i : Fin n, fourierCoeff f {i}) ^ 2 ≤
      ∑ a : X n, compProb f a * estZ a ^ 2) ∧
    (∑ a : X n, compProb f a * estZ a ^ 2 = n) := by sorry

end QCopyMono
