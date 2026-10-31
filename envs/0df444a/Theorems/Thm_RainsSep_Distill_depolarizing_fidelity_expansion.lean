-- Prove2me | Theorems.Thm_RainsSep_Distill_depolarizing_fidelity_expansion
-- name    : RainsSep.Distill.depolarizing_fidelity_expansion
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T16:00:16.371206+00:00
-- url     : https://prove2.me/theorems/7c6e1b73-8cbb-44c9-ab21-cd8946159100
-- title:
--   Eqs. (20)–(21): $\Delta(\epsilon)=f\rho(1)+\tfrac{1-f}{3}\sum\rho(\sigma)$ and $F_{\mathcal P}(\Delta^{\otimes n})=\sum_j f^{n-j}(\tfrac{1-f}{3})^jB_j$
-- statement:
--   Let $\epsilon$ be real and $f=1-\tfrac34\epsilon$. Then:
--
--   1. $\Delta(\epsilon)=f\,\rho(1)+\frac{1-f}{3}\big(\rho(\sigma_x)+\rho(\sigma_y)+\rho(\sigma_z)\big)$ as operators on one pair of qubits;
--   2. $F(\Delta(\epsilon))=f$;
--   3. for every $n$, $K$ and every map of Kraus form $\mathcal P(\rho)=\sum_i E_i\rho E_i^\dagger$ from two $n$-qubit registers to $\mathbb C^K\otimes\mathbb C^K$,
--
--   $$
--   F\big(\mathcal P(\Delta(\epsilon)^{\otimes n})\big)=\sum_{j=0}^n f^{n-j}\Big(\frac{1-f}{3}\Big)^j B_j(\mathcal P),\qquad B_j(\mathcal P)=\sum_{\mathrm{wt}(E)=j}F_{\mathcal P}(E).
--   $$
--
--   The output fidelity on $n$ depolarizing pairs is thus the polynomial $B$ evaluated at $(f,(1-f)/3)$; all later bounds are bounds on the coefficients $B_j$.
--
--   Differences from the source:
--   - generalization: Eq. (21) for the fixed separable superoperator P of Eq. (13) → every Kraus-form map Σ_i E_i(·)E_i† on n qubit pairs, normalized or not, separable or not; reason: both sides are linear in the map; taking E_i = P_i(1) ⊗ P_i(2) gives the source's statement
--   - generalization: Δ(ε) a state (0 ≤ ε ≤ 4/3) → every real ε; reason: all three identities are polynomial in ε and specialize to the state range
--   - encoding: Eq. (20) as operators on a two-qubit space → stated for the one-pair power pairPower (Δ(ε)) 1 on Qubits 1 × Qubits 1; reason: the same matrix; the index type Bool is replaced by Fin 1 → Bool so both sides have one type
--   - encoding: V an n-qubit space, W of dimension K, an orthonormal basis, a bipartite V ⊗ V → Qubits n (bit strings of length n, false = |0⟩), W = Fin K, the first tensor factor Alice's, her qubit k paired with Bob's qubit k, computational bases, fidelity the real part of φ+† σ φ+; reason: a choice of labels: φ+ depends on the basis only up to local unitaries (p. 1), and the value is real on Hermitian operators
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eqs. (20)–(22), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_RainsSep_Distill_depolarizing
import Definitions.Def_RainsSep_Distill_pairPower
import Definitions.Def_RainsSep_Distill_choiState
import Definitions.Def_RainsSep_Distill_enumB

open QAlgorithms QAlgorithms.Stabilizer

namespace RainsSep.Distill

/-- **Eqs. (20)–(21): the Pauli expansion of `Δ(ε)` and the fidelity polynomial.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eqs. (20)–(22), p. 2: "We can also write ∆(ǫ) = f ρ(1) + ((1 − f)/3)(ρ(σx) + ρ(σy) +
ρ(σz)), (20) with f = 1 − (3/4)ǫ = F(∆(ǫ)). We can then write: F_P(∆(ǫ)^{⊗n}) = Σ_j f^{n−j}
((1 − f)/3)^j Σ_{wt(E)=j} F_P(E), (21)".

For every real `ε`, with `f = 1 − (3/4)ε`:
1. `Δ(ε) = f ρ(1) + ((1 − f)/3)(ρ(σx) + ρ(σy) + ρ(σz))` (one pair, `n = 1`);
2. `F(Δ(ε)) = f`;
3. for every `n`, `K` and every Kraus-form map `P = Σ_i E_i(·)E_i†` from `n` qubit pairs to
   `ℂ^K ⊗ ℂ^K`, `F(P(Δ(ε)^{⊗n})) = Σ_{j=0}^n f^{n−j} ((1−f)/3)^j B_j(P)`.

**Formalization Note.** (1) is stated for `pairPower (depolarizing ε) 1`, the one-pair operator on
`Qubits 1 × Qubits 1`, so that both sides live on the same index type. (3) holds for every
Kraus family, normalized or not, separable or not; `ε` is any real number. -/
theorem depolarizing_fidelity_expansion (ε f : ℝ) (hf : f = 1 - (3 / 4) * ε) :
    pairPower (depolarizing ε) 1 =
        (f : ℂ) • choiState (pauliOps ![Pauli.I]) +
          (((1 - f) / 3 : ℝ) : ℂ) • (choiState (pauliOps ![Pauli.X]) +
            choiState (pauliOps ![Pauli.Y]) + choiState (pauliOps ![Pauli.Z])) ∧
      entFidelity (depolarizing ε) = f ∧
      ∀ (n K m : ℕ) (E : Fin m → Matrix (Fin K × Fin K) (Qubits n × Qubits n) ℂ),
        entFidelity (krausApply E (pairPower (depolarizing ε) n)) =
          ∑ j ∈ Finset.range (n + 1), f ^ (n - j) * ((1 - f) / 3) ^ j * enumB (krausApply E) j := by sorry

end RainsSep.Distill
