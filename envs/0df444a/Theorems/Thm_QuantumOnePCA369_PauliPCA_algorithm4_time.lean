-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_algorithm4_time
-- name    : QuantumOnePCA369.PauliPCA.algorithm4_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:44.812193+00:00
-- url     : https://prove2.me/theorems/d1f717d4-1459-436e-8c32-c76fdfa4a1b7
-- title:
--   Lemma 4.4 — Algorithm 4 runs in $\tilde O(2^n/(\Delta\varepsilon)\cdot\mathrm{poly}(\eta/(\Delta\varepsilon))\log(1/\delta))$ time (corrected: $\log(1/\delta)$ near $\delta=1$)
-- statement:
--   For every value of the constant $C_M$ of Algorithm 4 there are universal constants $C,a$ such that for all $n\ge1$, $0<\Delta\le1$, $0<\varepsilon\le\eta$ and $\delta>0$, every exact eigensolver and every run, Algorithm 4 runs in time at most
--   $$C\,\Big\lceil\frac{2^n}{\Delta\varepsilon}\Big(\frac{\eta}{\Delta\varepsilon}\Big)^{a}L^{a}D\Big\rceil,$$
--   with $L=n+\log(2+1/\varepsilon)+\log(2+1/\Delta)+\log(2+\eta)$ and $D=\log(2+1/\delta)$.
--
--   This is the running-time half of Theorem 1.1: when the gap is constant and $\eta/\varepsilon=O(1)$ it is nearly linear in the dimension $2^n$.
--
--   Running time is the tick count of the program in the unit-cost real RAM of §2 (p. 5): one tick per real or complex arithmetic operation, square root, logarithm, ceiling, comparison, array read or write and loop step, $n$ ticks per measured copy, and one call of an exact eigensolver on a $d'\times d'$ Hermitian matrix charged $d'^3+1$. The cubic charge is a chosen polynomial envelope for this idealized primitive, not a bit-complexity or numerical-stability claim.
--
--   **Formalization Note** The parameter range is that of Lemma 4.3: $\varepsilon\le\eta$, and $\Delta$ is a lower bound on the spectral gap of a state, hence $\Delta\le1$.
--
--   Differences from the source:
--   - correction: factor log(1/δ) in the Õ-bound, for all δ > 0 → factor D = log(2 + 1/δ); reason: log(1/δ) → 0 as δ → 1 forces N = 0 for δ close to 1, which is false: for n = 2 and a pure state (λ = Δ = 1, η = ε < 1) an algorithm with no copies succeeds with probability at most ε^3 for some state, while 1 − δ = τ can be chosen larger than ε^3; D ≤ 2 log(1/δ) for δ ≤ 1/2, so nothing changes in the range the paper means
--   - encoding: Õ(·) and poly(η/(Δε)), suppressing logarithmic factors in 1/ε, 1/Δ, η, 2^n → ≤ C·⌈(2^n/(Δε))·(η/(Δε))^a·L^a·D⌉ with universal C, a; reason: a power of L dominates the logarithms; (η/(Δε))^a dominates any polynomial since η/(Δε) ≥ 1 here
--   - reading: Algorithm 4 runs in time Õ(…) (no parameter range stated in Lemma 4.4) → 0 < Δ ≤ 1 and 0 < ε ≤ η; reason: Lemma 4.4 analyses Algorithm 4 in the setting of Lemma 4.3 (ε ≤ η; Δ at most the gap of a state, so Δ ≤ 1); for Δ ≫ 1 the printed bound falls below 2^n while the loops of Algorithm 4 still take order 2^n steps
--   - generalization: Algorithm 4 with its constant in M = O(…) → every value of C_M, every eigensolver, every run; reason: the bound holds for whichever constant line 3 uses; the source's algorithm is one instance
--   - encoding: running time in the real RAM model with spectral computations' numerical details omitted (p. 5) → tick count of the defined program: one tick per scalar operation, comparison, array access and loop step, n ticks per measured copy, an exact eigensolver charged d'^3 + 1; reason: §2 defers spectral computations to the real RAM model; the cubic charge is a polynomial envelope and the paper's bounds only use poly(d')
--   - encoding: an n-qubit state → 1 ≤ n; reason: Algorithm 4 (lines 5 and 13) needs a first qubit
--   - encoding: ε, δ > 0 arbitrary → if ε ≥ 1 or δ ≥ 1 the algorithm measures no copy and returns the basis vector |0…0⟩ after a constant number of charged steps; reason: for ε ≥ 1 every unit vector satisfies the fidelity requirement and for δ ≥ 1 the requirement is vacuous; no positive ε or δ is excluded
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 18, Lemma 4.4; Algorithm 4, p. 15

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_Protocol
import Definitions.Def_QuantumOnePCA369_PauliPCA_SubspacePruning

namespace QuantumOnePCA369.PauliPCA

theorem algorithm4_time :
    ∀ CM : ℝ, ∃ C a : ℝ, ∀ (ch : SpectralChooser) (n : ℕ) (Δ η ε δ : ℝ),
      1 ≤ n → 0 < Δ → Δ ≤ 1 → 0 < ε → ε ≤ η → 0 < δ →
      ∀ (r : (alg4 ch CM n Δ η ε δ).Rand) (y : (alg4 ch CM n Δ η ε δ).Copy → Bits n),
        ((alg4 ch CM n Δ η ε δ).runTime r y : ℝ) ≤
          C * ⌈(2 : ℝ) ^ n / (Δ * ε) * (η / (Δ * ε)) ^ a * polylogL n Δ η ε ^ a * confD δ⌉₊ := by sorry

end QuantumOnePCA369.PauliPCA
