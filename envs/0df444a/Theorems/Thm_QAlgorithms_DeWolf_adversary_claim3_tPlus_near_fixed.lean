-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_adversary_claim3_tPlus_near_fixed
-- name    : QAlgorithms.DeWolf.adversary_claim3_tPlus_near_fixed
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:44:30.511563+00:00
-- url     : https://prove2.me/theorems/9b457707-0bf7-4289-a1cd-36b7366741a5
-- title:
--   |t⁺_x⟩ is within 0.01 of an eigenvalue-1 eigenvector of U_x
-- statement:
--   Let $f : D \to \{0,1\}$ with $D \subseteq \{0,1\}^N$ and let $\{u_{xj}, v_{xj}\}$, $u_{xj}, v_{xj} \in \mathbb C^d$, be a feasible solution of the dual SDP for $\mathrm{ADV}^{\pm}(f)$ with objective value $A > 0$. Work on three registers: the first spanned by $|0\rangle$ and $|j\rangle$, $j \in [N]$; the second one qubit; the third spanned by $|0\rangle, |1\rangle, \dots, |d\rangle$, with the vectors $u_{xj}, v_{xj}$ placed in $\mathrm{span}\{|1\rangle, \dots, |d\rangle\}$. Define
--
--   $$
--   |t^\pm_x\rangle = \tfrac{1}{\sqrt2}\left(|0\rangle|0\rangle|0\rangle \pm |1\rangle|f(x)\rangle|0\rangle\right), \qquad |\psi_y\rangle = \frac{0.01}{\sqrt A}|t^-_y\rangle - \sum_j |j\rangle|\bar y_j\rangle|v_{yj}\rangle,
--   $$
--
--   where $\bar y_j = 1 - y_j$. Let $\Lambda$ be the projector onto the orthogonal complement of $\mathrm{span}\{|\psi_y\rangle : y \in D\}$, let $\Pi_x$ be the projector onto the span of the basis states with $|j\rangle|x_j\rangle$ in the first two registers or $|0\rangle$ in the third, and let $U_x = (2\Pi_x - I)(2\Lambda - I)$.
--
--   Then for every $x \in D$ there is a nonzero vector $|\phi\rangle$ with $U_x|\phi\rangle = |\phi\rangle$ and
--
--   $$
--   \big\| |\phi\rangle - |t^+_x\rangle \big\| \le 0.01.
--   $$
--
--   This is the first of the two spectral facts that let phase estimation on $U_x$ distinguish $|t^+_x\rangle$ from $|t^-_x\rangle$.
--
--   **Formalization Note** The source's informal "close" is pinned to the distance $0.01$ its proof gives; as in the source, $|\phi\rangle$ need not be normalized. The objects are the fields of `AdvAlg`, whose `A` is exactly the objective value; $A > 0$ is needed for $1/\sqrt A$.
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 115, §12.3, Claim 3. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Adversary
set_option autoImplicit false

namespace QAlgorithms.DeWolf





/-- de Wolf §12.3, Claim 3 (PDF p. 115): for a feasible dual solution with objective value
`A > 0` and every `x ∈ D`, the state `|t^+_x⟩` is within Euclidean distance `0.01` of a
(nonzero, not necessarily normalized) eigenvector `|ϕ⟩` of `U_x = (2Π_x − I)(2Λ − I)` with
eigenvalue `1`. The constant `0.01` is the one the source's proof gives. -/
theorem adversary_claim3_tPlus_near_fixed {N : ℕ} (P : AdvAlg N)
    (hfeas : DualFeasibleDeWolf P.f P.D P.d P.u P.v) (hA : 0 < P.A) (x : P.D) :
    ∃ φ : AdvSpace N P.d, φ ≠ 0 ∧ P.walk x φ = φ ∧ ‖φ - P.tPlus x‖ ≤ 1 / 100 := by
  sorry


end QAlgorithms.DeWolf
