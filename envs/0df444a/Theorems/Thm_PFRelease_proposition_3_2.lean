-- Prove2me | Theorems.Thm_PFRelease_proposition_3_2
-- name    : PFRelease.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:53.864204+00:00
-- url     : https://prove2.me/theorems/0d8b8687-cb07-4c9a-8644-52af3610b550
-- title:
--   Proposition 3.2 — privacy of fixed-threshold sparse vector
-- statement:
--   Let $n,\kappa\in\mathbb N$, $\delta\in(0,1)$, $\varepsilon\in(0,4\ln(2/\delta)]$, a threshold $t\in\mathbb R$, and adaptive queries $q_1,\dots,q_n$ of sensitivity at most $1$: each query may depend on the preceding transcript, and for every fixed prefix its values on neighbouring datasets differ by at most $1$. If $\kappa\ge12\ln(2/\delta)$, then fixed-threshold sparse vector $\mathrm{SV}_{t,\kappa,\sigma}$ (Algorithm 2) is $(\varepsilon,\delta)$-DP, where
--   $$
--   \sigma:=\frac{7\sqrt{\kappa\ln(2/\delta)}}{\varepsilon}.
--   $$
--
--   The privacy cost is governed by the cap $\kappa$ on the number of failures, not by the number of queries; this is what lets the filter test every record.
--
--   **Formalization Note** Datasets are an arbitrary type with an arbitrary neighbour relation; zero-out adjacency on $n$-slot datasets is the instance used by the paper. The number of queries is independent of the size of the datasets (the page uses $n$ for both).
--
--   Differences from the source:
--   - generalization: datasets under zero-out adjacency → an arbitrary type of datasets with an arbitrary neighbour relation `Adj`; reason: the statement only uses the sensitivity bound of the queries on neighbouring pairs; taking `Adj` to be zero-out adjacency gives the source's claim
--   - encoding: adaptive queries $q_i$ depending on $(u_1,\dots,u_{i-1})$ → `q i u d`, the value on $d$ of the $i$th query chosen after the prefix $u$, with the sensitivity bound for every list $u$; reason: same queries; values at lists that are not prefixes of a run are never used, so a family of the source can be set constant there without changing the law
--   - encoding: $n$ both the number of queries and the dataset size → the number of queries $n$ is independent of the dataset type; reason: the page uses one letter for two independent quantities
--   - encoding: the noises $\gamma_i$ drawn inside the loop → all $n$ noises drawn in advance (`svLaw` is the image of $\mathrm{Lap}(\sigma)^{\otimes n}$); reason: unused noises do not change the law of the transcript
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Proposition 3.2, p.9 (PDF p.11); restated as Proposition B.3, p.31

import Mathlib
import Definitions.Def_PFRelease_Indist
import Definitions.Def_PFRelease_svLaw

open MeasureTheory

namespace PFRelease

/-- **Proposition 3.2 (Privacy of fixed-threshold sparse vector)** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Proposition 3.2,
p.9 = PDF p.11; restated as Proposition B.3, p.31). Given `n, κ ∈ ℕ`, `δ ∈ (0, 1)`,
`ε ∈ (0, 4 ln(2/δ)]`, a threshold `t ∈ ℝ` and adaptive queries `q₁, …, qₙ` of sensitivity at most
1, if `κ ≥ 12 ln(2/δ)`, then `SV_{t,κ,σ}` (Algorithm 2) is `(ε, δ)`-DP, where
`σ := 7√(κ ln(2/δ))/ε`.

**Formalization Note** Datasets form an arbitrary type `D` with an arbitrary neighbour relation
`Adj` (a declared generalization; zero-out adjacency on `Fin N → Option X` is an instance). The
query `q i u` is the `i`th query chosen after the preceding transcript `u`; sensitivity at most 1
means `|q i u d − q i u d′| ≤ 1` for every prefix `u` and every neighbouring pair. The number of
queries `n` is independent of the size of the datasets. The conclusion compares the transcript laws
`svLaw` on every neighbouring pair. -/
theorem proposition_3_2 {D : Type*} (Adj : D → D → Prop) (n κ : ℕ) (δ ε t : ℝ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hε0 : 0 < ε) (hε1 : ε ≤ 4 * Real.log (2 / δ))
    (q : Fin n → List Bool → D → ℝ)
    (hq : ∀ (i : Fin n) (u : List Bool) (d d' : D), Adj d d' → |q i u d - q i u d'| ≤ 1)
    (hκ : 12 * Real.log (2 / δ) ≤ κ) :
    ∀ d d' : D, Adj d d' →
      Indist (svLaw t κ (7 * Real.sqrt (κ * Real.log (2 / δ)) / ε) q d)
        (svLaw t κ (7 * Real.sqrt (κ * Real.log (2 / δ)) / ε) q d') ε δ := by sorry

end PFRelease
