-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_qubitObjectiveTwo_eq_closedForm
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.qubitObjectiveTwo_eq_closedForm
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-27T20:56:26.579094+00:00
-- url     : https://prove2.me/theorems/106f1cba-6d48-4a12-a638-3b3f5c8becf9
-- title:
--   §VII.A, Lemma 10 (step 1): closed form of the second qubit objective
-- statement:
--   Let $0<\beta\le 1/2$ and $\beta<T\le 1-\beta$, put $\eta=1-\beta-T$, and for $t\in[-1,1]$ let $P(t)=\frac12\begin{pmatrix}1+t&\sqrt{1-t^2}\\sqrt{1-t^2}&1-t\end{pmatrix}$ be the pure-state projector of Audenaert–Eisert's objective (45). Define $x=\beta-T+\eta t$, $y^2=\eta^2(1-t^2)$, $r_\sigma=\sqrt{x^2+y^2}$, $r_\rho=\sqrt{(x+2T)^2+y^2}$, $w=\dfrac{(x+2T)\,x+y^2}{r_\sigma}$, and
--
--   $$\Phi(t)=\sum_{\pm}\frac{1\pm r_\rho}{2}\log\frac{1\pm r_\rho}{2}\;-\;\sum_{\pm}\frac{1\pm w}{2}\log\frac{1\pm r_\sigma}{2}.$$
--
--   Let $\rho_t=\operatorname{diag}(\beta+T,0)+\eta P(t)$ and $\sigma_t=\operatorname{diag}(\beta,T)+\eta P(t)$. Then the relative entropy satisfies
--
--   $$D(\rho_t\|\sigma_t)=\operatorname{Tr}\big[\rho_t(\log\rho_t-\log\sigma_t)\big]=\Phi(t)\qquad(t\in[-1,1]).$$
--
--   This expresses the second qubit objective of Lemma 10 through the eigenvalues $(1\pm r_\rho)/2$ and $(1\pm r_\sigma)/2$ of the two unit-trace qubit matrices, reducing Lemma 10 to a one-variable statement.
--
--   **Formalization note.** Logarithms are natural, $0\log 0=0$, and Lean's conventions $\log 0=0$ and $a/0=0$ apply (so $w=0$ when $r_\sigma=0$, which happens only for $T=1/2$, $t=1$). The unit vector defining $P(t)$ is $(\sqrt{(1+t)/2},\sqrt{(1-t)/2})$, as in the definition `qubitObjectiveTwo`.
-- source:
--   Continuity bounds on the quantum relative entropy, Audenaert–Eisert, arXiv:quant-ph/0503218v3, PDF pp. 9–10, §VII.A, Lemma 10 and its proof (objective (45))

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.10, proof of Lemma 10: closed form of objective (45) through the
eigenvalues `(1 ± r)/2` of the two unit-trace qubit matrices. -/
theorem qubitObjectiveTwo_eq_closedForm (beta T t : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2)
    (hT : beta < T ∧ T ≤ 1 - beta) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    qubitObjectiveTwo beta T t =
      (let x := beta - T + (1 - beta - T) * t
       let y2 := (1 - beta - T) ^ 2 * (1 - t ^ 2)
       let rs := Real.sqrt (x ^ 2 + y2)
       let rr := Real.sqrt ((x + 2 * T) ^ 2 + y2)
       let w := ((x + 2 * T) * x + y2) / rs
       (1 + rr) / 2 * Real.log ((1 + rr) / 2) + (1 - rr) / 2 * Real.log ((1 - rr) / 2) -
         ((1 + w) / 2 * Real.log ((1 + rs) / 2) + (1 - w) / 2 * Real.log ((1 - rs) / 2))) := by
  sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
