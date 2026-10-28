-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P40_shorLaflamme_relation
-- name    : QAlgorithms.Papers.Independent.Support50.P40.shorLaflamme_relation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T22:03:13.59206+00:00
-- url     : https://prove2.me/theorems/10748c0c-0fd3-49f1-b731-b0da5f86de3e
-- title:
--   Coset weight polynomials and Shor–Laflamme enumerators
-- statement:
--   Let $p\ge0$ and let $C$ be a finite set of canonical Hermitian $p$-qubit Pauli labels, with scalar phases discarded. Write $w(e)$ for the number of nonidentity factors, $g=(1-f)/3$ for $f\in[0,1]$, and $P_f(C)=\sum_{e\in C}f^{p-w(e)}g^{w(e)}$. Using ordinary matrix traces, define $A_d(O_1,O_2)=\sum_{w(u)=d}\operatorname{tr}(uO_1)\operatorname{tr}(uO_2)$ and $A(z,O_1,O_2)=\sum_{d=0}^p A_d(O_1,O_2)z^d$.
--
--   Then, for every Pauli label $e$ and nonnegative integer $d$,
--
--   $$
--   A_d(e,e)=4^p\mathbf1_{\{w(e)=d\}},\qquad
--   P_f(C)=4^{-p}\sum_{e\in C}\sum_{d=0}^p A_d(e,e)f^{p-d}g^d.
--   $$
--
--   For $f>0$ one also has
--
--   $$
--   P_f(C)=\frac{f^p}{4^p}\sum_{e\in C}A(g/f,e,e)
--   =\left(\frac f4\right)^p\sum_{e\in C}A\left(\frac{1-f}{3f},e,e\right).
--   $$
--
--   This identifies the probability polynomials with the earlier enumerators. The division-free formula remains valid at $f=0$.
--
--   **Formalization Note** The first double sum in printed Eq. (6) omits $4^{-p}$. The statement includes the normalization forced by Eq. (5) and both right-hand expressions; independent moderation of this correction remains required.
-- source:
--   Quantum Channel Capacity of Very Noisy Channels, arXiv:quant-ph/9706061v3, PDF p. 7, Section II, Eqs. (5)-(6): relation to Shor-Laflamme enumerators

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P40

namespace QAlgorithms.Papers.Independent.Support50.P40

open QAlgorithms QAlgorithms.Stabilizer

open scoped ComplexConjugate Matrix

noncomputable section

/-- PDF p.7, Eqs.(5)--(6). Source correction: the first double sum in
printed Eq.(6) omits `4^(-p)`; Eq.(5) and both right-hand expressions force
this factor. The polynomial identity includes f=0; only the ratio form
requires f>0. No quantum-state hypothesis is needed for matrix enumerators. -/
theorem shorLaflamme_relation (p : ℕ) (C : Finset (ErrorLabel p))
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    (∀ (e : ErrorLabel p) (d : ℕ),
      slWeight d (pauliOps e) (pauliOps e) =
        if opsWeight e = d then (4 : ℂ) ^ p else 0) ∧
    ((weightPolynomial f C : ℂ) = ((4 : ℂ) ^ p)⁻¹ *
      ∑ e ∈ C, ∑ d ∈ Finset.range (p + 1),
        slWeight d (pauliOps e) (pauliOps e) * (f : ℂ) ^ (p - d) * (noiseG f : ℂ) ^ d) ∧
    (0 < f →
      (weightPolynomial f C : ℂ) = (f : ℂ) ^ p / (4 : ℂ) ^ p *
        ∑ e ∈ C, slEnumerator ((noiseG f : ℂ) / (f : ℂ)) (pauliOps e) (pauliOps e) ∧
      (weightPolynomial f C : ℂ) = ((f : ℂ) / 4) ^ p *
        ∑ e ∈ C, slEnumerator (((1 - f) / (3 * f) : ℝ) : ℂ) (pauliOps e) (pauliOps e)) := by sorry

end

end QAlgorithms.Papers.Independent.Support50.P40
