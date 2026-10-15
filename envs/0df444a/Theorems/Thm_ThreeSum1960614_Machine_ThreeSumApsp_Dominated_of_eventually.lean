-- Prove2me | Theorems.Thm_ThreeSum1960614_Machine_ThreeSumApsp_Dominated_of_eventually
-- name    : ThreeSum1960614.Machine.ThreeSumApsp.Dominated.of_eventually
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:11:42.752319+00:00
-- url     : https://prove2.me/theorems/9f148f10-f958-484b-b138-e3ecf254c634
-- title:
--   Eventual domination extends over a positive tail
-- statement:
--   Let $f,g:\mathbb N\to\mathbb R$, with $f(n)\le Cg(n)$ eventually. If $g(n)>0$ for every $n\ge n_0$, then $f$ is dominated by $g$ on that whole tail in the framework sense.
--
--   This tail-extension result makes eventual asymptotic comparisons usable in solver contracts requiring bounds on a full tail.
-- source:
--   https://github.com/Anchen0823/three-sum-1960614/blob/8c25c0325de5be4286413f39ca0c9278aad33f52/Submission/ThreeSumApsp/Util/Asymptotics/Dominated.lean#L248-L267

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Lean
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Asymptotics
end Asymptotics
namespace Filter
end Filter
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSum1960614.Machine.ThreeSumApsp.Dominated
end ThreeSum1960614.Machine.ThreeSumApsp.Dominated
namespace ThreeSumApsp
end ThreeSumApsp
namespace ThreeSumApsp.Dominated
end ThreeSumApsp.Dominated

open _root_.Filter
open _root_.Asymptotics
open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp

open _root_.ThreeSum1960614.Machine.ThreeSumApsp.Dominated

variable {α β : Type*} {dom dom' : α → Prop} {f f' g g' h k f₁ f₂ g₁ g₂ : α → ℝ}

theorem ThreeSum1960614.Machine.ThreeSumApsp.Dominated.of_eventually {f g : ℕ → ℝ} {C : ℝ} (hfg : ∀ᶠ n in atTop, f n ≤ C * g n) {n₀ : ℕ}
    (hg : ∀ n, n₀ ≤ n → 0 < g n) : _root_.ThreeSum1960614.Machine.ThreeSumApsp.Dominated (fun n => n₀ ≤ n) f g := by sorry
