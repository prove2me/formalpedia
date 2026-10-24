-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P02_erasure_side_information
-- name    : QAlgorithms.Papers.Independent.Support50.P02.erasure_side_information
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:18:31.015164+00:00
-- url     : https://prove2.me/theorems/e834c428-21bd-436b-ad0f-4a4b1390aa53
-- title:
--   §6: no extra cq corner for erasure MAC
-- statement:
--   Let $d,k\ge1$ and let $\mathcal E_d$ be the controlled-erasure MAC that flags Alice's computational-basis outcome $0$ and coherently transfers Bob's $d$-dimensional input on outcome $1$. Fix any pure ensemble on Alice's $k$ inputs and an independent pure Bob reference/input pair, and let $\sigma^{XBC^k}$ be their output under $\mathcal E_d^{\otimes k}$. If $I_c(B\rangle C^k)_\sigma\ge0$, then the new cq corner lies in the old rectangle for that very state:
--   $$\bigl(I(X;BC^k)_\sigma,I_c(B\rangle C^k)_\sigma\bigr)\in\{(u,v)\ge0:u\le I(X;C^k)_\sigma,\ v\le I_c(B\rangle C^kX)_\sigma\}.$$
--   This is pointwise for every positive blocklength and every such input, without optimization. The hypothesis precisely restricts the claimed corner to nonnegative operational rates; negative information coordinates are not in the source's rate rectangles.
-- source:
--   Capacity Theorems for Quantum Multiple Access Channels: Classical-Quantum and Quantum-Quantum Capacity Regions, arXiv:quant-ph/0501045v3, PDF p. 31, §6: no extra cq corner for erasure MAC

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P02

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Support50.P02

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity receiverChannel complementaryChannel IsDegradable)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C E R S I J : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype E] [DecidableEq E]

variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- No extra erasure cq corner, PDF p.31, with the channel defined on pp.32–33.
This is pointwise at EVERY positive blocklength, not merely optimized-region equality.
The new corner is an operational rate pair when its quantum coordinate is nonnegative;
negative information corners are not elements of the source's nonnegative rectangles. -/
theorem erasure_side_information (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (D : CQMacData (Fin n → Bool) (Fin n → Fin d))
    (hcorner : 0 ≤ D.coherent (macPower (controlledErasure d) n)) :
    D.Rectangle (macPower (controlledErasure d) n)
      (D.sideClassical (macPower (controlledErasure d) n),
        D.coherent (macPower (controlledErasure d) n)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P02

end
