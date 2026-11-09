-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_bloch_inner_eq
-- name    : QuantumMaxCutEnergy.bloch_inner_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-08T19:26:00.701862+00:00
-- url     : https://prove2.me/theorems/4d3aed9f-6f9a-47af-98c8-469ef69768de
-- title:
--   Two-qubit correlation identity: $2|\beta_a\alpha_b-\alpha_a\beta_b|^2 = 1-\langle r_a,r_b\rangle$
-- statement:
--   **The two-qubit correlation identity.**
--
--   Let $(\alpha_a,\beta_a)$ and $(\alpha_b,\beta_b)$ be normalised amplitude pairs, $|\alpha|^2+|\beta|^2=1$, with Bloch vectors $r_a=r(\alpha_a,\beta_a)$, $r_b=r(\alpha_b,\beta_b)$ as defined above. Then
--   $$2\,\big|\beta_a\alpha_b-\alpha_a\beta_b\big|^2 \;=\; 1-\langle r_a,r_b\rangle .$$
--
--   **Why it matters.** For a product state $\psi=\bigotimes_i(\alpha_i|0\rangle+\beta_i|1\rangle)$, the energy of an edge $\{a,b\}$ in the Quantum Max-Cut Hamiltonian is $\tfrac{w}{2}\sum_x|\psi(x)-\psi(x\circ\mathrm{swap}_{ab})|^2$. Writing $x$ out over the two swapped coordinates, the inner sum is exactly $2|\beta_a\alpha_b-\alpha_a\beta_b|^2$ — there are only two contributing terms, each of modulus $|\beta_a\alpha_b-\alpha_a\beta_b|$, and the diagonal terms cancel. By the identity that equals $1-\langle r_a,r_b\rangle$. Summing over edges,
--   $$\mathrm{energy}(\psi)=\sum_e \frac{w_e}{2}\big(1-\langle r_{e_1},r_{e_2}\rangle\big)=\tfrac14\sum_{i,j}A_{ij}\big(1-\mathrm{gram}(r)_{ij}\big)=\mathrm{obj}(\mathrm{gram}\,r),$$
--   i.e. the classical relaxation objective at the Gram matrix of the Bloch vectors **is** the quantum energy of the corresponding product state. Since `optimum` is a supremum over all normalised states, this makes $\mathrm{obj}(\mathrm{gram}\,r)\le\texttt{optimum}$ automatic for every Bloch assignment — the "each candidate is sound" conjunct of the rounding estimator, for free.
--
--   **Proof.** Pure algebra. With $\alpha=\alpha_r+i\alpha_i$, $\beta=\beta_r+i\beta_i$ and $p=|\alpha|^2$, $q=|\beta|^2$, $z=\bar\alpha\beta$, one has $|r|^2=(p+q)^2$ and
--   $$1-\langle r_a,r_b\rangle=1-4\operatorname{Re}(z_a\bar z_b)-(p_a-q_a)(p_b-q_b),$$
--   while
--   $$|\beta_a\alpha_b-\alpha_a\beta_b|^2=q_ap_b+p_aq_b-2\operatorname{Re}(z_a\bar z_b).$$
--   Using $p_i+q_i=1$ to rewrite $1-(p_a-q_a)(p_b-q_b)=2p_aq_b+2q_ap_b$, the two expressions agree. No trigonometry is involved.
-- source:
--   Product-state energy of the Quantum Max Cut Hamiltonian; Bloch-sphere correlation identity. Anshu-Gosset-Morenz, TQC 2020, doi 10.4230/LIPIcs.TQC.2020.7.

import Mathlib
import Definitions.Def_QuantumMaxCutEnergy_bloch

open Complex
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **The two-qubit correlation identity.** -/
theorem bloch_inner_eq (αa βa αb βb : ℂ)
    (ha : Complex.normSq αa + Complex.normSq βa = 1)
    (hb : Complex.normSq αb + Complex.normSq βb = 1) :
    2 * Complex.normSq (βa * αb - αa * βb)
      = 1 - (bloch αa βa 0 * bloch αb βb 0 + bloch αa βa 1 * bloch αb βb 1
          + bloch αa βa 2 * bloch αb βb 2) := by sorry

end QuantumMaxCutEnergy
