-- Prove2me | Theorems.Thm_PhosphorylationSharpness_conversion_root
-- name    : PhosphorylationSharpness.conversion_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:22:53.64789+00:00
-- url     : https://prove2.me/theorems/6e0c933c-f515-474f-8632-29cd020f581d
-- title:
--   Phosphorylation Sharpness: conversion root
-- statement:
--   The Phosphorylation Sharpness construction uses the conversion root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L159-L167
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean#L159-L167

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
set_option autoImplicit true
open PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology

theorem PhosphorylationSharpness.conversion_root (p q : ℝ[X]) (r x : ℝ)
    (hx : (x-1)*p.eval (ratio x)-2*q.eval (ratio x)=0) :
    (x-1)*((rawB p q r).eval (ratio x)-r*(rawD p q r).eval (ratio x)) =
      2*(r-ratio x)*(rawD p q r).eval (ratio x) := by sorry
