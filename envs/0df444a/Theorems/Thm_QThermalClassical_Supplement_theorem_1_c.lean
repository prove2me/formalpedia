-- Prove2me | Theorems.Thm_QThermalClassical_Supplement_theorem_1_c
-- name    : QThermalClassical.Supplement.theorem_1_c
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:40:28.186602+00:00
-- url     : https://prove2.me/theorems/9ccd84a3-be70-43f2-8363-ef5aae4e7760
-- title:
--   Theorem 1(c) — $(s,\gamma)$-nonlocal Gibbs states are separable for $\beta\le\min\{\gamma/(16s),1/(16s)\}$, and $w$-bounded nonlocal Hamiltonians can stay entangled at every constant temperature
-- statement:
--   1. Let $s,\gamma>0$. For every $n$ and every $(s,\gamma)$-nonlocal Pauli Hamiltonian $H$ on $n$ qubits, the Gibbs state $\rho_\beta(H)$ is separable whenever
--   $$
--   0\le\beta\le\min\Big\{\frac{\gamma}{16s},\frac1{16s}\Big\}.
--   $$
--   2. Let $w:\mathbb N\to\mathbb R$ be non-decreasing with $w(n)=e^{o(n)}$, i.e. $w>0$ and $\log w(n)=o(n)$. There is a sequence of Pauli Hamiltonians $H_n=\sum_a c_aP_a$ on $n$ qubits and a constant $C$ with
--   $$
--   \max_{x\in[n]}\sum_{a:\ x\in\mathrm{supp}(P_a)}|c_a|\,w(|\mathrm{supp}(P_a)|)\le C\qquad\text{for all } n,
--   $$
--   such that for every constant $\beta>0$ the Gibbs state $\rho_\beta(H_n)$ is entangled for all sufficiently large $n$.
--
--   So an exponential decay of coefficients in the support size forces separability at a constant temperature, while any subexponential weight does not.
--
--   Differences from the source:
--   - reading: for every constant $\beta>0$ … there is a sequence $H_n$ … whose Gibbs states are entangled at all constant temperatures (i.e., $\beta$ independent of $n$) → one sequence for all $\beta$: $\forall w,\ \exists (H_n),\ \forall\beta>0,\ \exists N,\ \forall n\ge N$, $\rho_\beta(H_n)$ entangled; reason: the parenthesis says the sequence works at every constant temperature; the sequence-first order implies the $\beta$-first one; 'entangled' for a family indexed by $n$ is read eventually in $n$, as in Theorem 37
--   - reading: $w(n)=e^{o(n)}$; $=O(1)$ → $w>0$ and $\log w(n)=o(n)$; a bound $C$ uniform in $n$ and $x$; reason: $w=e^{f}$ with $f=o(n)$ is exactly this; $O(1)$ over the sequence
--   - encoding: Pauli Hamiltonian $H=\sum_{a\in A}c_aP_a$ on $n$ qubits with distinct non-identity strings → coefficient function $c$ on Pauli words of `Fin n` with $c(I)=0$, $A=\{P:c_P\neq0\}$; reason: distinctness is automatic and words with coefficient $0$ change neither $H$ nor any condition; no instance changes
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 1(c), eqs. (26)–(27), p.14

import Mathlib
import Definitions.Def_QThermalClassical_ham
import Definitions.Def_QThermalClassical_gibbs
import Definitions.Def_QThermalClassical_IsSeparable
import Definitions.Def_QThermalClassical_Supplement_weightedStrength
import Definitions.Def_QThermalClassical_Supplement_IsNonlocalPauli

set_option autoImplicit false

namespace QThermalClassical.Supplement

/-- **Theorem 1(c) (Death of entanglement, nonlocal Pauli Hamiltonians).**
1. For every `n`, all `s, γ > 0` and every `(s, γ)`-nonlocal Pauli Hamiltonian `H` on `n`
   qubits, `ρ_β(H)` is separable whenever `0 ≤ β ≤ min{γ/(16s), 1/(16s)}` (26).
2. For every non-decreasing `w : ℕ → ℝ` with `w(n) = e^{o(n)}` (`w > 0`, `log w(n) = o(n)`)
   there is a sequence of Pauli Hamiltonians `H_n` on `n` qubits with
   `max_x Σ_{a : x ∈ supp P_a} |c_a| w(|supp P_a|) = O(1)` (27), uniformly in `n`, whose Gibbs
   states `ρ_β(H_n)` are entangled for every constant `β > 0` once `n` is large enough.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Theorem 1(c), eqs. (26)–(27), p.14.

**Formalization Note.** "Entangled at all constant temperatures (i.e., `β` independent of
`n`)" is: one sequence, chosen before `β`, such that for each `β > 0` the Gibbs state is
entangled for all `n ≥ N(β)`. `O(1)` is a bound `C` uniform in `n` and `x`. -/
theorem theorem_1_c :
    (∀ (n : ℕ) (s γ : ℝ), 0 < s → 0 < γ → ∀ c : PauliWord (Fin n) → ℝ,
      IsNonlocalPauli s γ c → ∀ β : ℝ, 0 ≤ β → β ≤ min (γ / (16 * s)) (1 / (16 * s)) →
        IsSeparable (gibbs (ham c) β)) ∧
    (∀ w : ℕ → ℝ, Monotone w → (∀ m, 0 < w m) →
      (fun m : ℕ => Real.log (w m)) =o[Filter.atTop] (fun m : ℕ => (m : ℝ)) →
      ∃ c : ∀ n : ℕ, PauliWord (Fin n) → ℝ, (∀ n, c n (fun _ => 0) = 0) ∧
        (∃ C : ℝ, ∀ (n : ℕ) (x : Fin n), weightedStrength w (c n) x ≤ C) ∧
        ∀ β : ℝ, 0 < β → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬ IsSeparable (gibbs (ham (c n)) β)) := by sorry

end QThermalClassical.Supplement
