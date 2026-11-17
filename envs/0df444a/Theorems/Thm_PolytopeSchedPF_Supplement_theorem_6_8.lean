-- Prove2me | Theorems.Thm_PolytopeSchedPF_Supplement_theorem_6_8
-- name    : PolytopeSchedPF.Supplement.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:25:03.16291+00:00
-- url     : https://prove2.me/theorems/39bb0582-08c1-4ec8-93d4-c8264e7d88e8
-- title:
--   Theorem 6.8 — every polytope between a $c$-sparse binary polytope and its integer hull admits a $c$-approximate certificate for all weights
-- statement:
--   Let $\mathcal Q=\{y\in\mathbb R^n_{\ge0}: By\le\mathbf 1\}$ be a $c$-sparse binary polytope ($c\in\mathbb N$; Definition 6.7) with integer hull $\mathcal Q_{\mathrm{int}}$, and let $\mathcal P$ be a downward-closed polytope with
--
--   $$\mathcal Q_{\mathrm{int}}\subseteq\mathcal P\subseteq\mathcal Q.$$
--
--   Then for every weight vector $w\in\mathbb R^n_{>0}$, $\mathcal P$ admits a $c$-approximate certificate for $w$ (Definition 6.1).
--
--   With $c=2$, $\mathcal Q$ the fractional matching polytope and $\mathcal P$ the matching polytope, this combined with Theorem 6.3 gives the graph-scheduling guarantee of Theorem 1.7.
--
--   Differences from the source:
--   - encoding: a c-sparse binary polytope Q and a downward-closed polytope P with Q_int ⊆ P ⊆ Q → base RatePolytopes Q (D rows) and P (D′ rows) with intHull Q ⊆ P.rates ⊆ Q.rates; reason: base reading R1; P contains every unit vector (each is a 0/1 point of Q), so it has such a description
--   - encoding: admits a c-approximate certificate for all weights → for every w with all entries positive, AdmitsApproxCertificate P w c; reason: Definition 6.1 takes w ∈ ℝⁿ>0
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, Theorem 6.8, §6.2, p.37 (PDF p.39); Definition 6.7, p.37 (PDF p.39); Definition 6.1, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_PolytopeSchedPF_Supplement_ApproxCertificate
import Definitions.Def_PolytopeSchedPF_Supplement_SparseBinary

namespace PolytopeSchedPF

namespace Supplement

/-- **Theorem 6.8** (Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §6.2, p.37). Let `Q` be a
`c`-sparse binary polytope. Every downward-closed polytope `P` with `Q_int ⊆ P ⊆ Q` admits a
`c`-approximate certificate for all weights.

**Formalization Note** `Q` and `P` are base `RatePolytope`s (reading R1), with possibly different
numbers of rows `D`, `D'`; the inclusions are between their rate sets. "For all weights" is every
`w ∈ ℝⁿ_{>0}` (Definition 6.1). -/
theorem theorem_6_8 {n D D' : ℕ} (c : ℕ) (Q : RatePolytope n D) (hQ : IsSparseBinary Q c)
    (P : RatePolytope n D') (hint : intHull Q ⊆ P.rates) (hPQ : P.rates ⊆ Q.rates) :
    ∀ w : Fin n → ℝ, (∀ j, 0 < w j) → AdmitsApproxCertificate P w (c : ℝ) := by sorry

end Supplement

end PolytopeSchedPF
