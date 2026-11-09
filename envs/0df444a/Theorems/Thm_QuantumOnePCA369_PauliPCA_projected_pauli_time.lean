-- Prove2me | Theorems.Thm_QuantumOnePCA369_PauliPCA_projected_pauli_time
-- name    : QuantumOnePCA369.PauliPCA.projected_pauli_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:37:49.960896+00:00
-- url     : https://prove2.me/theorems/f0aac9c9-f774-454b-8e18-f2b27e57dfcc
-- title:
--   Lemma 3.4 — Algorithm 2 runs in $O(2^n n^2k^2R)$ time (corrected: $n$ to $n+1$)
-- statement:
--   Let $n=\ell+m$, $k\ge1$ and $k_0\le2k$. There is a universal constant $C$ such that for all pairs $(A_r,c_r)\in\mathrm{Sym}_m(\mathbb F_2)\times\mathbb F_2^m$, $r<R$, and all $2^m\times k_0$ matrices $\tilde U_s$, Algorithm 2 runs in time at most
--   $$C\,2^n(n+1)^2k^2R.$$
--
--   The nearly linear dependence on $2^n$ comes from the two Walsh–Hadamard passes; it is what keeps the whole tomography step nearly linear in the dimension.
--
--   Running time is the tick count of the program in the unit-cost real RAM of §2 (p. 5): one tick per real or complex arithmetic operation, square root, logarithm, ceiling, comparison, array read or write and loop step, $n$ ticks per measured copy, and one call of an exact eigensolver on a $d'\times d'$ Hermitian matrix charged $d'^3+1$. The cubic charge is a chosen polynomial envelope for this idealized primitive, not a bit-complexity or numerical-stability claim.
--
--   Differences from the source:
--   - correction: O(2^n n² k² R) → ≤ C · 2^n (n+1)² k² R; reason: at n = 0 (ℓ = m = 0) and R ≥ 1 the program executes at least one loop step while 2^0·0·k²R = 0; for n ≥ 1 the bounds agree up to a factor 4
--   - encoding: k_0 ≤ 2k with k the subspace dimension → 1 ≤ k and k_0 ≤ 2k; reason: k² = 0 at k = 0 would make any positive cost exceed the bound; k is a positive dimension
--   - generalization: partial unitaries Ũ_s → arbitrary complex 2^m × k_0 matrices; reason: the running time does not depend on the entries; the source's case is a special case
--   - encoding: running time in the real RAM model with spectral computations' numerical details omitted (p. 5) → tick count of the defined program: one tick per scalar operation, comparison, array access and loop step, n ticks per measured copy, an exact eigensolver charged d'^3 + 1; reason: §2 defers spectral computations to the real RAM model; the cubic charge is a polynomial envelope and the paper's bounds only use poly(d')
--   - encoding: prefix s ∈ {0,1}^ℓ on the first ℓ qubits, Ũ_s of size 2^{n−ℓ} × k_0 → separate prefix and suffix lengths ℓ and m with ℓ + m = n; Ũ_s : 2^m × k_0; reason: m = n − ℓ without natural-number subtraction
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, p. 9, Lemma 3.4; Algorithm 2, p. 8

import Mathlib
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic
import Definitions.Def_QuantumOnePCA369_PauliPCA_ProjectedPauli

namespace QuantumOnePCA369.PauliPCA

theorem projected_pauli_time :
    ∃ C : ℝ, ∀ (n ℓ m k k₀ R : ℕ) (A : Fin R → SymF2 m) (c : Fin R → Bits m)
      (U : Bits ℓ → Matrix (Bits m) (Fin k₀) ℂ),
      ℓ + m = n → 1 ≤ k → k₀ ≤ 2 * k →
      ((alg2 ℓ m k₀ R A c U).cost : ℝ) ≤ C * 2 ^ n * (n + 1) ^ 2 * k ^ 2 * R := by sorry

end QuantumOnePCA369.PauliPCA
