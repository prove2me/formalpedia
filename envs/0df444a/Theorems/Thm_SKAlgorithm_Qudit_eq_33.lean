-- Prove2me | Theorems.Thm_SKAlgorithm_Qudit_eq_33
-- name    : SKAlgorithm.Qudit.eq_33
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:07.617535+00:00
-- url     : https://prove2.me/theorems/173ea296-d030-4fa7-a9b1-9eb961c147fa
-- title:
--   Eq. (33), pp. 11–13 — balanced approximate group commutators in SU(d)
-- statement:
--   Fix $d$. There are constants $c_{gc'} > 0$ and $c_{gc''} > 0$ such that for every $\epsilon > 0$ and every $U \in SU(d)$ with $d(I, U) < \epsilon$ there exist $V, W \in SU(d)$ with
--   $$d(VWV^\dagger W^\dagger, U) < c_{gc'}\, \epsilon^{3/2}, \qquad d(I, V),\ d(I, W) < c_{gc''} \sqrt{\epsilon} .$$
--
--   This is the guarantee of GC-Approx-Decompose in the qudit algorithm: a gate near the identity is approximated, to order $\epsilon^{3/2}$, by a group commutator of two gates at distance $O(\sqrt\epsilon)$ from the identity. The paper's constants are $c_{gc''} \approx d^{1/4}((d-1)/2)^{1/2}$ and $c_{gc'} \approx 4 d^{3/4}((d-1)/2)^{3/2}$.
--
--   **Formalization Note.** The constants are existential, chosen before $\epsilon$ and $U$, and may depend on $d$; the approximate values are not pinned. $V$ and $W$ are required to lie in $SU(d)$, since the algorithm recurses on them. The paper's derivation on pp. 12–13 contains a sign slip: with $[F, G] = iH$ and $U = \exp(iH)$, Lemma 3 gives $VWV^\dagger W^\dagger \approx \exp(i \cdot i[F,G]) = \exp(-iH) = U^\dagger$, not $U$. The statement of Eq. (33) is nevertheless true (apply Lemma 2 to $-H$, or exchange $F$ and $G$), and it is stated as the paper claims it.
-- source:
--   Dawson and Nielsen, The Solovay-Kitaev algorithm, arXiv:quant-ph/0505030v2, p. 11, §5.2 (goal of the subsection); p. 13, Eq. (33); p. 10, §5.1, properties (a)–(b)

import Mathlib
import Definitions.Def_SKAlgorithm_Qudit_Model

open scoped Matrix
open QAlgorithms

namespace SKAlgorithm.Qudit

theorem eq_33 (d : ℕ) :
    ∃ c' c'' : ℝ, 0 < c' ∧ 0 < c'' ∧ ∀ ε : ℝ, 0 < ε → ∀ U : SU d, opDist 1 U < ε →
      ∃ V W : SU d, opDist (V * W * V⁻¹ * W⁻¹) U < c' * ε ^ ((3 : ℝ) / 2) ∧
        opDist 1 V < c'' * Real.sqrt ε ∧ opDist 1 W < c'' * Real.sqrt ε := by sorry

end SKAlgorithm.Qudit
