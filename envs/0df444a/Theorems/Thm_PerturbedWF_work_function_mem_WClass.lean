-- Prove2me | Theorems.Thm_PerturbedWF_work_function_mem_WClass
-- name    : PerturbedWF.work_function_mem_WClass
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:42:42.112499+00:00
-- url     : https://prove2.me/theorems/88a64064-60fc-45e9-a88f-6c1f19c30ccf
-- title:
--   §2 and Appendix B: the metric-allocation work functions $W_t$ belong to $\mathcal W(\mathcal C)$
-- statement:
--   Consider metric allocation on the simplex $\mathcal C$ over a finite metric $d$, with initial configuration $x_0\in\mathcal C$ and separable service costs $F_t(x)=\sum_if_{t,i}(x_i)$ for $t=1,\dots,N$, every $f_{t,i}:[0,1]\to\mathbb R_{\ge0}$ convex and continuous. Then for every $0\le t\le N$ the work function $W_t$ of (4.1) belongs to $\mathcal W(\mathcal C)$: its domain is nonempty and compact (here it is all of $\mathcal C$), it is 1-Lipschitz, and it satisfies the exchange property.
--
--   The paper states this for all its problems on p.6 and proves the exchange property in Appendix B by writing $W_t$ as a flow model (B.1) and applying Lemma B.1(1). Every general lemma of the analysis (2.3, 2.4, 3.2) applies to $W_t$ through this fact.
--
--   **Formalization Note.** The reduced requests $F_t(x)=f_t(x_{r_t})$ of the rest of the mission are the separable case $f_{t,r_t}=f_t$, $f_{t,i}=0$ for $i\ne r_t$. The identification of (4.1) with the flow model is part of the proof, not of the statement.
--
--   Differences from the source:
--   - reading: service costs F_q = Σ_i f_{q,i} with f_{q,i} convex, used as arc costs φ_a : ℝ≥0 → ℝ (lower semicontinuous) in the flow model of p.33 → F_t = Σ_i f_{t,i} on the simplex with every f_{t,i} real-valued, convex, continuous and nonnegative on [0, 1] (IsSepReq); reason: Appendix B's arc costs are real-valued and lower semicontinuous; a real convex lower semicontinuous function on [0, 1] is continuous; nonnegativity is §4's F_t : C → ℝ≥0
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), §2 'Work functions', p.6 (PDF p.7); Appendix B, paragraph 'Metric allocation', p.33 (PDF p.34)

import Mathlib
import Definitions.Def_PerturbedWF_MetricAllocation

namespace PerturbedWF

/-- **Metric-allocation work functions lie in `W(C)`**: §2, p.6 (PDF p.7), "It will be obvious for
all the problems we consider that work functions have nonempty, compact domains … and are
1-Lipschitz. In Appendix B, we show for each problem that they additionally satisfy the exchange
property, and hence belong to `W(C)`", for metric allocation as modelled in Appendix B, paragraph
"Metric allocation", p.33 (PDF p.34). C. Coester, D. Kashaev, *Online Metric Problems via Randomly
Perturbed Work Functions*, STOC 2027 submission (held version, sha256 e2e30a44…).

For a finite metric `d`, an initial configuration `x₀` in the simplex and separable convex service
costs `F_t(x) = ∑_i f_{t,i}(x_i)` (`1 ≤ t ≤ N`, each `f_{t,i} : [0, 1] → ℝ_{≥0}` convex and
continuous), every work function `W_t` (`0 ≤ t ≤ N`) of (4.1), as a function `C → ℝ ∪ {∞}`,
belongs to `W(C)`.

**Formalization Note.** The service costs are real-valued, as are the arc costs `φ_a = f_{q,i}`
of the flow model of p.33 (Appendix B's arc costs are real and lower semicontinuous; a real convex
lower semicontinuous function on `[0, 1]` is continuous). The reduced requests of §4
(`F_t(x) = f_t(x_{r_t})`) are the case `f_{t,r_t} = f_t`, `f_{t,i} = 0` otherwise. The paper
derives the exchange property from the flow model (B.1) with Lemma B.1(1); identifying (4.1) with
the flow model is part of the proof, not of the statement. -/
theorem work_function_mem_WClass {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (hd : IsFinMetric d) (x₀ : ι → ℝ) (hx₀ : x₀ ∈ simplex ι) (N : ℕ)
    (F : ℕ → (ι → ℝ) → ℝ) (hF : ∀ t ∈ Finset.Icc 1 N, IsSepReq (F t)) (t : ℕ) (ht : t ≤ N) :
    WClass (simplex ι) d (fun x => ((workFn d x₀ F t x : ℝ) : EReal)) := by sorry

end PerturbedWF
