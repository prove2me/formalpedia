-- Prove2me | Theorems.Thm_SemisimpleQFT_standard_gt_exists
-- name    : SemisimpleQFT.standard_gt_exists
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-19T15:59:03.912551+00:00
-- url     : https://prove2.me/theorems/36306a53-d23b-40dc-b320-5671cb2f7e8a
-- title:
--   Theorem 4.17 with Section 5: subalgebra adapted Fourier bases in the orthogonal form exist
-- statement:
--   For each of the chains
--   $$\mathbb{C}\cong B_0(d)\subseteq B_1(d)\subseteq\dots\subseteq B_n(d)\quad(d\notin\{0,\dots,n\}),$$
--   $$B_{0,0}(d)\subseteq B_{1,0}(d)\subseteq B_{1,1}(d)\subseteq\dots\subseteq B_{r,r}(d)\subseteq B_{r,r+1}(d)\subseteq\dots\subseteq B_{r,s}(d)\quad(r\le s,\ d\notin\{0,\dots,r+s-2\}),$$
--   $$\mathbb{C}\cong P_0(d)\subseteq P_{1/2}(d)\subseteq P_1(d)\subseteq\dots\subseteq P_{n-1/2}(d)\subseteq P_n(d)\quad(d\notin\{0,\dots,2n-2\}),$$
--   there is a subalgebra adapted (Gelfand–Tsetlin) system of Fourier bases: every algebra of the chain is semisimple with irreps labelled by the Young diagrams (pairs of Young diagrams) of Theorems 4.12–4.15, the bases of the irrep spaces are indexed by the paths of the Bratteli diagram given by the branching rules of Theorem 5.2 and are adapted to the chain (Eqs. (5.7)–(5.8)); the basis of the top algebra is in the orthogonal form $\rho(D^{\mathrm{op}})=\rho(D)^\dagger$ (Eq. (5.25)); and the labelling of the top algebra satisfies Theorem 4.17: $\lambda(D)=0$ for every diagram $D$ with $\mathrm{pn}(D)<|\lambda|$.
-- source:
--   B. Foxman, B. Nehoran, Y. Ding, Efficient Quantum Fourier Transforms For Semisimple Algebras, https://arxiv.org/abs/2605.05337, pp. 25–26, 31, 34–35: Theorems 4.12, 4.14, 4.15, 4.17, 5.2, Eqs. (5.20)–(5.25)

import Definitions.Def_SemisimpleQFT_Chains

open scoped BigOperators ComplexConjugate

namespace SemisimpleQFT

theorem standard_gt_exists :
    (∀ n d : ℕ, n < d →
      ∃ G : GTSystem n (fun t => diagramAlgebra (brauerLevel n t) d) (brauerBratteli n),
        G.IsStandard Shape.size) ∧
    (∀ r s d : ℕ, r ≤ s → r + s < d + 2 →
      ∃ G : GTSystem (r + s) (fun t => diagramAlgebra (walledLevel r (r + s) t) d)
          (walledBratteli r (r + s)),
        G.IsStandard pairSize) ∧
    (∀ n d : ℕ, 2 * n < d + 2 →
      ∃ G : GTSystem (2 * n) (fun t => diagramAlgebra (partitionLevel n t) d)
          (partitionBratteli n),
        G.IsStandard Shape.size) := by sorry

end SemisimpleQFT
