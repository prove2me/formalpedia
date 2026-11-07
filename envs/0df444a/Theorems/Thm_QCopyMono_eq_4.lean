-- Prove2me | Theorems.Thm_QCopyMono_eq_4
-- name    : QCopyMono.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:12.109702+00:00
-- url     : https://prove2.me/theorems/159d5ed7-5467-4e3d-b4f7-97ce38d997de
-- title:
--   Eq. (4) — a monotone function has $I[g]\le\sqrt n$
-- statement:
--   Every monotone Boolean function $f:\{0,1\}^n\to\{0,1\}$ has total influence
--   $$
--   I[g]\le\sqrt n .
--   $$
--   This classical fact (cited to [ODo21, Section 2.3]) is what makes a coarse influence estimate a valid first filter: functions of influence much larger than $\sqrt n$ can be rejected outright.
--
--   Differences from the source: none.
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §3.1, p.7, eq. (4)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_Influence

namespace QCopyMono

open QAlgorithms

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §3.1, p.7, eq. (4) (cited to [ODo21,
Section 2.3]): every monotone Boolean function satisfies `I[g] ≤ √n`. -/
theorem eq_4 (n : ℕ) (f : Qubits n → Bool) (hf : Monotone f) :
    influence f ≤ Real.sqrt n := by sorry

end QCopyMono
