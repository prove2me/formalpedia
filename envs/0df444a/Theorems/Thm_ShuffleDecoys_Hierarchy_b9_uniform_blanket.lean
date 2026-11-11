-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_b9_uniform_blanket
-- name    : ShuffleDecoys.Hierarchy.b9_uniform_blanket
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:21.891266+00:00
-- url     : https://prove2.me/theorems/5f0addea-7458-4d93-a05f-74f8f7803f88
-- title:
--   Appendix B.9, proof of Theorem B.1 — the uniform blanket: χ²(W_m ‖ U_d^{⊗n}) = (d − 1)/n and sup_P I_P(M; Z) ≤ (d − 1)/n
-- statement:
--   Let $d\ge2$ and $n\ge1$. Take the canonical mechanism with the uniform blanket $Q=U_d$ (the $n-1$ decoys i.i.d. uniform on $[d]$, whatever the prior), let $R=Q^{\otimes n}$ be the reference law on $[d]^n$ and $W_m=\mathrm{Law}(Z\mid M=m)$. With $N_m(z)$ the number of occurrences of $m$ in $z$ and $q_m=1/d$,
--   $$\frac{dW_m}{dR}(z)=\frac{N_m(z)}{nq_m},\qquad \chi^2(W_m\,\|\,R)=\mathbb E_R\Big[\Big(\frac{N_m}{nq_m}-1\Big)^2\Big]=\frac{d-1}{n},\qquad \sup_{P\in\Delta_d}I_P(M;Z)\le\frac{d-1}{n}.$$
--   This is the upper half of $L_{\mathrm{can}}(d,n)=\Theta_d(n^{-1})$ in Theorem B.1, with an explicit constant valid at every $n$.
--
--   Differences from the source:
--   - reading: the paragraph fixes no range of $n$ → every $n\ge1$; reason: the model is defined for $n\ge1$ and the paragraph's computation holds for every such $n$.
--   - encoding: $dW_m/dR$ and $\chi^2(W_m\|R)$ → the mass identity $W_m(z)=R(z)\,N_m(z)/(nq_m)$ and the finite sum $\sum_z(W_m(z)-R(z))^2/R(z)$ with $R(z)=d^{-n}$; reason: definitions of the density and of $\chi^2$ for laws on a finite set with $R$ of full support.
--   - encoding: the uniform-blanket mechanism → any kernel $R$ with mass $d^{-(n-1)}$ on every decoy tuple at every message, and $W_m$ = release law under the prior $\delta_m$; reason: this is that mechanism and its conditional release law.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), pp. 46–47, Appendix B.9, proof of Theorem B.1, 'A uniform upper bound for canonical shuffling'

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Appendix B.9, proof of Theorem B.1, "A uniform upper bound for canonical shuffling": with the
uniform blanket `Q = U_d`, reference `R = Q^{⊗n}` and `W_m = Law(Z | M = m)`,
`dW_m/dR(z) = N_m(z)/(n q_m)`, `χ²(W_m ‖ R) = (d − 1)/n`, and `sup_P I_P(M; Z) ≤ (d − 1)/n`. -/
theorem b9_uniform_blanket (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n) (R : DecoyKernel (Fin d) n)
    (hR : ∀ m h, R m h = ∏ _i : Fin (n - 1), (d : ℝ≥0∞)⁻¹) :
    let W : Fin d → PMF (Fin n → Fin d) := fun m =>
      (shuffleExperiment (PMF.pure m) R).map shuffleOutput
    (∀ m : Fin d, ∀ z : Fin n → Fin d,
      (W m z).toReal = (1 / (d : ℝ)) ^ n *
        (((Finset.univ.filter fun i => z i = m).card : ℝ) / ((n : ℝ) * (1 / (d : ℝ))))) ∧
    (∀ m : Fin d,
      ∑ z : Fin n → Fin d, ((W m z).toReal - (1 / (d : ℝ)) ^ n) ^ 2 / (1 / (d : ℝ)) ^ n =
        ((d : ℝ) - 1) / n) ∧
    (⨆ P : PMF (Fin d), leakage P R) ≤ ENNReal.ofReal (((d : ℝ) - 1) / n) := by sorry

end ShuffleDecoys.Hierarchy
