-- Prove2me | Theorems.Thm_QNatProofs_corollary_4_6_2
-- name    : QNatProofs.corollary_4_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:06:19.352974+00:00
-- url     : https://prove2.me/theorems/9883e902-5bef-4c08-9692-9831ca065cad
-- title:
--   Corollary 4.6.2 — low-depth implementation of the PRAL family
-- statement:
--   Let $\mathcal G$ be a keyed family computable by polynomial-size depth-$d_F$ threshold circuits, $d_F\ge1$, let $a\in(0,1)$ and let $C\ge1$. Then the PRAL family of Theorem 3.4, built from $\mathcal G$ with exponent $a$ and the finite Poisson sampler of Lemma 4.1 at the parameters of p.25 (with the constant $C$), is efficiently $e^{-n}$-approximately $\mathrm{MH}_{8d_F+20}$-preparable: there is one QNC$^0$ depth $D$ and one polynomial $q$ such that for every $n,\lambda,T$ and every $|\psi\rangle$ in the support of $D_{n,\lambda,T}$, some circuit at level $8d_F+20$ (depth $D$) of size at most $q(n+\lambda+T)$ has reduced output state within trace distance $e^{-n}$ of $|\psi\rangle\langle\psi|$.
--
--   This is the preparability half of the main theorem.
--
--   Differences from the source:
--   - reading: A_kCQ / MH_k (defined in [Par25], not in the paper) → MHLevel k D: C₀Q₁C₁⋯Q_kC_k with Clifford segments C_i of any length and one- and two-qubit unitary segments Q_i of depth ≤ D; reason: the paper's own level counts (p.25: [Cliff][A₄][Cliff][A₄][Cliff] ⊆ A₈; p.40: A₁ = Clifford then QNC⁰) fix this form; A_kCQ ⊆ MH_k on p.22
--   - generalization: the functions of 𝒢 are computable by polynomial-size depth-d_F threshold circuits → ThresholdComputable: one polynomial p, and for every m and key k some threshold circuit of depth ≤ d_F and size ≤ p(m) computes G_{m,k}; the circuit may depend on the key; reason: weaker hypothesis: a circuit taking the key as input gives these by fixing the key bits; the proof fixes the key (p.33)
--   - generalization: the subexponentially secure PRF family 𝒢 used in Theorem 3.4 → any keyed family 𝒢 and any exponent a ∈ (0, 1); security is not assumed; reason: preparability does not use security; the theorem specializes to the secure 𝒢 with its exponent
--   - encoding: the resulting PRAL family → pralFamily 𝒢 a (poissonSF C): the construction of Theorem 3.4's proof with the finite Poisson sampler at the parameters of p.25 and any C ≥ 1; reason: the family is defined once and shared with Theorem 3.4 and Theorem 4.7
--   - encoding: a designated n-qubit output register; the other qubits traced out → the first n wires; the partial trace over the remaining wires (reducedOutput); reason: any designation is a renaming of wires, which changes neither size nor level
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Corollary 4.6.2, p.33; proof p.33

import Mathlib
import Definitions.Def_QNatProofs_MHLevel
import Definitions.Def_QNatProofs_ThrCircuit
import Definitions.Def_QNatProofs_pralFamily

set_option autoImplicit false

namespace QNatProofs

/-- **Corollary 4.6.2 (Low-depth implementation of the PRAL family)** (Li, Parham, *Natural proofs
for quantum state preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.33;
proof p.33): "Suppose the subexponentially secure PRF family `𝒢` used in Theorem 3.4 is computable
by polynomial-size depth-`d_F` TC⁰ circuits. Then the resulting PRAL family is efficiently
`e^{-n}`-approximately `MH_{8d_F+20}`-preparable."

The resulting PRAL family is `pralFamily 𝒢 a (poissonSF C)`: the construction of Theorem 3.4's
proof (p.17) with the finite Poisson sampler of Lemma 4.1 at the parameters of p.25, for the PRF
exponent `a ∈ (0, 1)` and the constant `C ≥ 1` of Theorem 3.1. Here `d_F ≥ 1` (Theorem 4.7).

**Formalization Note** `MH_k` is `MHLevel k D` for one QNC⁰ depth `D`, fixed before `n, λ, T` and
the state. Preparability does not use the security of `𝒢`, so security is not assumed; the
threshold circuits may depend on the key. -/
theorem corollary_4_6_2 (G : KeyedFam) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (C : ℝ) (hC : 1 ≤ C)
    (dF : ℕ) (hdF : 1 ≤ dF) (hthr : G.ThresholdComputable dF) :
    ∃ D : ℕ, EffApproxPreparable (pralFamily G a (poissonSF C)) (MHLevel (8 * dF + 20) D)
      (fun n => Real.exp (-(n : ℝ))) := by sorry

end QNatProofs
