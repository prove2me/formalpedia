-- Prove2me | Theorems.Thm_RobustPower_CostGap_instance_symmetric
-- name    : RobustPower.CostGap.instance_symmetric
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:13:00.844088+00:00
-- url     : https://prove2.me/theorems/676163ab-d0df-4fa7-841a-4d949a8534f6
-- title:
--   Proof of Theorem 3.1, pp. 22–23 — the instance is symmetric about (1, (1/2, …, 1/2)) and satisfies (2.1)
-- statement:
--   Let $n\ge1$, let $(\Omega,\mu)$ be a probability space and let $d:\Omega\to\mathbb R^n$ be measurable, with range exactly the cube $[0,1]^n$, and such that the coordinates $d_1,\dots,d_n$ are independent and uniformly distributed on $[0,1]$ (the law of $d$ under $\mu$ is the product of the uniform distributions on $[0,1]$). Put $b(\omega)=1\in\mathbb R^1$ for every $\omega$, so that the uncertainty set is $I_{(b,d)}(\Omega)=\{(b(\omega),d(\omega)):\omega\in\Omega\}=\{1\}\times[0,1]^n$. Then
--
--   $$
--   I_{(b,d)}(\Omega)\ \text{is symmetric about}\ \bigl(1,(\tfrac12,\dots,\tfrac12)\bigr)\qquad\text{and}\qquad \mathbb E_\mu[d(\omega)]=(\tfrac12,\dots,\tfrac12).
--   $$
--
--   In particular the scenario $\omega^0$ at the point of symmetry has $b(\omega^0)=1$ and $d(\omega^0)=(\tfrac12,\dots,\tfrac12)=\mathbb E_\mu[d(\omega)]$, so the measure satisfies the paper's condition (2.1). This shows that the large gap of Theorem 3.1 occurs under the symmetry hypotheses that suffice, for right-hand-side uncertainty alone, to bound the gap by 2.
--
--   **Formalization Note** The uncertainty set lives in $\mathbb R^1\times\mathbb R^n$, and symmetry is Definition 1.2 in that product group; the expectation of $d$ is the Bochner integral of the vector-valued map $\omega\mapsto d(\omega)$.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, pp. 22–23, proof of Theorem 3.1 (first paragraph)

import Mathlib
import Definitions.Def_RobustPower_StochGap_SymmetricSets

open MeasureTheory

namespace RobustPower.CostGap

/-- Proof of Theorem 3.1, pp. 22–23: the uncertainty set `{(b(ω), d(ω))} = {1} × [0, 1]ⁿ` is
symmetric about `(1, (1/2, …, 1/2))`, and `E_μ[d(ω)] = (1/2, …, 1/2)`, so (2.1) holds. -/
theorem instance_symmetric {n : ℕ} (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : Ω → Fin n → ℝ) (hd : Measurable d) (hrange : Set.range d = Set.Icc 0 1)
    (hlaw : μ.map d = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1))) :
    RobustPower.StochGap.IsSymmetricAbout (Set.range fun ω => ((fun _ => 1 : Fin 1 → ℝ), d ω))
        ((fun _ => 1 : Fin 1 → ℝ), (fun _ => 1 / 2 : Fin n → ℝ)) ∧
      ∫ ω, d ω ∂μ = (fun _ => 1 / 2 : Fin n → ℝ) := by sorry

end RobustPower.CostGap
