-- Prove2me | Theorems.Thm_WHMultiplicativity_isChannel_wernerHolevo
-- name    : WHMultiplicativity.isChannel_wernerHolevo
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:12.513573+00:00
-- url     : https://prove2.me/theorems/e02e5046-6622-4b79-a737-9630d45070c1
-- title:
--   §II, p.2: the Werner–Holevo map $S$ is a channel (linear, completely positive, trace preserving)
-- statement:
--   Let $d \ge 2$. The map on complex $d\times d$ matrices
--
--   $$
--   S(\rho) = \frac{1}{d-1}\Big(\operatorname{tr}(\rho)\,\mathbb 1 - \rho^T\Big)
--   $$
--
--   is a quantum channel: it is linear, completely positive and trace preserving. Equivalently, there are finitely many matrices $E_1,\dots,E_m$ with $\sum_j E_j^*E_j = \mathbb 1$ and $S(\rho) = \sum_j E_j\rho E_j^*$ for every $\rho$.
--
--   This is the hypothesis that makes $S$ admissible in the multiplicativity conjecture, which is stated for channels.
--
--   **Formalization Note** "Channel" is `QAlgorithms.IsChannel`, the existence of a finite normalized Kraus family representing the map on every matrix; in finite dimension this is exactly complete positivity plus trace preservation (Choi–Kraus).
--
--   Differences from the source:
--   - encoding: S is linear, trace preserving and completely positive → QAlgorithms.IsChannel (wernerHolevo d): a finite Kraus family with Σ_j E_jᴴ E_j = 1 representing S on every matrix; reason: Choi–Kraus: in finite dimension these are the same maps
--   - encoding: matrix transpose and conjugates with respect to some fixed basis → the standard basis of ℂ^d (index Fin d); reason: any fixed basis; the statement is the same up to a unitary change of basis
--   - encoding: d × d matrices with denominator d − 1 (d ≥ 2 implicit) → hypothesis 2 ≤ d; reason: excludes only d = 1, where the page's formula divides by zero
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, §II, p.2 (sentence after eq. (7))

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model

open WHAdditivity.Renyi

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, §II, p.2 (after eq. (7)): the map `S` of (6) is
a channel: "In the first form it is easy to verify that S is linear and trace preserving, in the
second it becomes clear that it is also completely positive."

**Formalization Note.** "Channel" (linear, completely positive, trace preserving) is
`QAlgorithms.IsChannel`: `S` agrees on every matrix with `ρ ↦ Σ_j E_j ρ E_jᴴ` for a finite
family of Kraus operators with `Σ_j E_jᴴ E_j = 𝟙`, which in finite dimension is exactly CPTP
(Choi–Kraus). `2 ≤ d` is the paper's standing assumption (at `d = 1` Lean's `0⁻¹ = 0` makes
`wernerHolevo 1` the zero map, which is not trace preserving). -/
theorem isChannel_wernerHolevo (d : ℕ) (hd : 2 ≤ d) :
    QAlgorithms.IsChannel (wernerHolevo d) := by sorry

end WHMultiplicativity
