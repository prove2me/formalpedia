-- Prove2me | Theorems.Thm_StabTestMem_haar_vs_mixed
-- name    : StabTestMem.haar_vs_mixed
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:14:35.146323+00:00
-- url     : https://prove2.me/theorems/4e32e654-27f6-45a1-8054-f002e88d408d
-- title:
--   Theorem B.3 — Haar random states versus the maximally mixed state
-- statement:
--   1. There is an absolute constant $c>0$ such that if $t^2<c\,2^n$, then for every adaptive protocol with $k$ qubits of memory using $t$ single copies,
--
--   $$\mathbb E_{x\sim P_{\mathrm{mm}}}\big[|L(x)-1|\big]\le\frac{t^2}{2^n}+2^{3/2-(n-k-15\log t)/2}, \tag{223}$$
--
--   where $L(x)=\operatorname{Tr}[E_x\rho_H]/P_{\mathrm{mm}}(x)$ and $\rho_H=\mathbb E_\psi[\psi^{\otimes t}]$ for a Haar random pure state.
--
--   2. Consequently $t=2^{\Omega(n-k)}$ copies are required to distinguish a Haar random state from the maximally mixed state: there is $c'>0$ such that every protocol whose acceptance probabilities on $\rho_{\mathrm{mm}}$ and on a Haar random pure state differ by at least $1/3$ uses $t\ge2^{c'(n-k)}$ copies.
--
--   Together with Theorem 5.9 this gives the lower bound of Theorem 1.1, since a stabilizer tester separates phase states (stabilizer) from Haar random states (far from stabilizer).
--
--   Differences from the source:
--   - encoding: Definition 3.7: instruments in rounds 1, …, t−1 and a final POVM; adaptive single-copy protocol with a k-qubit memory → an instrument in every round (the last one's output memory discarded), a deterministic decision on the transcript, a finite outcome type; reason: a POVM {E^x} is the instrument Y ↦ Tr(E^x Y)η_*; randomness is absorbed into outcomes
--   - encoding: Tr[R(O)E_x], P_mm(x) = Tr[E_x]/2^{nt}, L(x) → the transcript functional P.weight evaluated at R(O), ρ_mm, σ (avgDev); reason: Lemma 3.10's E_x extended linearly to every t-copy operator
--   - generalization: t copies are required to distinguish (success ≥ 2/3 on each hypothesis) → any protocol whose acceptance probabilities on the two hypotheses differ by ≥ 1/3 has t ≥ …; reason: 2/3-correctness on each hypothesis gives an acceptance gap ≥ 1/3, so the Lean statement specializes to the paper's
--   - encoding: log t → Real.logb 2 t (log base 2; value 0 at t = 0); reason: the bound comes from t^{2r} = 2^{2r log t} (Lemma B.2); at t = 0, 1 both sides are trivial
--   - reading: t = 2^{Ω(n−k)} → ∃ c' > 0 with t ≥ 2^{c'(n−k)} for all n, k, t (no threshold); reason: the stronger reading; protocols with t ≤ 1 have acceptance gap 0 (ρ_H = ρ_mm for t ≤ 1)
--   - encoding: a Haar random state → integral against haarTargetLaw n (normalized complex Gaussian vector); reason: the unitarily invariant law on unit vectors
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Theorem B.3, Eq. (223), p. 64 (L as in Eq. (224))

import Definitions.Def_StabTestMem_avgDev
import Definitions.Def_StabTestMem_rhoH

namespace StabTestMem

open QAlgorithms MeasureTheory

/-- **Theorem B.3: Haar random states versus the maximally mixed state.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Theorem B.3, p. 64:
"There is an absolute constant c > 0 such that if t^2 < c2^n, then, for any protocol using k-qubits
of memory and single-copy measurements, E_{x∼P_mm}[|L(x) − 1|] ≤ t^2/2^n + 2^{3/2−(n−k−15 log t)/2}.
(223) Consequently, t = 2^{Ω(n−k)} samples are required to distinguish between a Haar random state
and the maximally mixed state." Here `L(x) = P_H(x)/P_mm(x)` (Eq. (224)).

(1) There is `c > 0` such that every adaptive protocol with `k` memory qubits and `t` copies with
`t² < c·2ⁿ` has `E_{x∼P_mm}|L(x) − 1| ≤ t²/2ⁿ + 2^{3/2 − (n − k − 15 log₂ t)/2}`. (2) There is
`c' > 0` such that every protocol whose acceptance probabilities on `ρ_mm` and on a Haar random
pure state differ by at least `1/3` uses `t ≥ 2^{c'(n−k)}` copies.

**Formalization Note.** `log` is `log₂` (`Real.logb 2`; the bound comes from `t^{2r} = 2^{2r log t}`,
Lemma B.2); `Real.logb 2 0 = 0` at `t = 0`. In (2), "distinguish" is generalized to an acceptance gap
`≥ 1/3`. The acceptance probability on a Haar random state is the integral against
`haarTargetLaw n`. Constants are uniform in `n, k, t` and the protocol. -/
theorem haar_vs_mixed :
    (∃ c : ℝ, 0 < c ∧ ∀ (n k t : ℕ) (X : Type) [Fintype X] (P : MemProtocol n k t X),
      (t : ℝ) ^ 2 < c * 2 ^ n →
        avgDev P (rhoH n t) ≤
          (t : ℝ) ^ 2 / 2 ^ n + (2 : ℝ) ^ ((3 : ℝ) / 2 - ((n : ℝ) - k - 15 * Real.logb 2 t) / 2)) ∧
    (∃ c' : ℝ, 0 < c' ∧ ∀ (n k t : ℕ) (X : Type) [Fintype X] (P : MemProtocol n k t X),
      1 / 3 ≤ |P.acceptProbOp (rhoMM n t) -
          ∫ ψ, P.acceptProb (ObliviousRSP.pureState ψ) ∂(TwoBasisCertification.haarTargetLaw n)| →
        (2 : ℝ) ^ (c' * ((n : ℝ) - k)) ≤ t) := by sorry

end StabTestMem
