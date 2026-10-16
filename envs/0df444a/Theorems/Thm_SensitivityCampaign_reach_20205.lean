-- Prove2me | Theorems.Thm_SensitivityCampaign_reach_20205
-- name    : SensitivityCampaign.reach_20205
-- status  : Proved
-- author  : @Leo Shaposhnik
-- created : 2026-10-16T00:04:46.279303+00:00
-- url     : https://prove2.me/theorems/5cd504de-db5d-4194-856a-e53a707196ec
-- title:
--   Separation exponent at least 2.0205
-- statement:
--   For every epsilon > 0 and every integer S ≥ 2, some total Boolean function f satisfies s(f) ≥ S and bs(f) ≥ s(f)^(2.0205−epsilon).
--
--   Independent statement read-back:
--
--   The declaration asserts that for every real number $\varepsilon>0$ and every natural number $S\ge 2$, there exist a natural number $n$ and a total Boolean function $f:\{0,1\}^{n}\to\{0,1\}$ such that $S\le s(f)$ and $s(f)^{4041/2000-\varepsilon}\le \operatorname{bs}(f)$, where the decimal $2.0205$ denotes the exact real number $20205/10000=4041/2000$, both natural-valued quantities in the power inequality are cast to real numbers, and the power is real exponentiation. The coordinates are indexed by $\operatorname{Fin}(n)=\{0,\ldots,n-1\}$. For an input $x$ and a subset $B$ of coordinates, $x^{B}$ denotes the input obtained by complementing exactly the coordinates in $B$. Explicitly, $s(f)=\max_{x\in\{0,1\}^{n}}|\{i\in\operatorname{Fin}(n):f(x^{\{i\}})\ne f(x)\}|$, and $\operatorname{bs}(f)$ is the maximum, over all inputs $x$ and all finite sets $\mathcal B$ of coordinate subsets, of $|\mathcal B|$ when distinct members of $\mathcal B$ are pairwise disjoint and every $B\in\mathcal B$ is nonempty and satisfies $f(x^{B})\ne f(x)$; a family failing these conditions contributes $0$ to that maximum. The family $\mathcal B=\varnothing$ is allowed and contributes $0$. The quantifier over $n$ includes $n=0$; its input space contains the unique empty assignment, and both sensitivities are $0$, so it cannot supply a witness satisfying $S\le s(f)$ with $S\ge2$. Thus every witnessing function has positive sensitivity at least $2$, including when $\varepsilon$ makes the real exponent zero or negative. Each function is defined on every Boolean assignment of its finite dimension, with no restricted or promise domain. The witnesses $n$ and $f$ may depend on both $\varepsilon$ and $S$; no single function or common dimension is required to work for all choices.
-- source:
--   Refinement of OpenAI/math, commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a, lean/OAI/Combinatorics/Sensitivity; local proof snapshot f142fafe7b0ad4f46d209a530ee057421fe0f374, Sharp.Certificate finite_certificate_20205 and Sharp.Asymptotic rational_family_20205.

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_finite_certificate
import Theorems.Thm_SensitivityCampaign_finite_certificate_log
open OAI.Paper320

theorem SensitivityCampaign.reach_20205 :
    SensitivityCampaign.AchievesExponent (2.0205 : ℝ) := by sorry
