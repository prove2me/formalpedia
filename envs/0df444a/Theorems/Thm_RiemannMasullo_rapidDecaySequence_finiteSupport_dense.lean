-- Prove2me | Theorems.Thm_RiemannMasullo_rapidDecaySequence_finiteSupport_dense
-- name    : RiemannMasullo.rapidDecaySequence_finiteSupport_dense
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T02:46:51.165179+00:00
-- url     : https://prove2.me/theorems/f14439c2-1708-46fd-897b-3cbe91366e0e
-- title:
--   Finitely supported sequences are dense in the rapidly decreasing lattice sequences
-- statement:
--   Every rapidly decreasing complex lattice sequence is a limit of finite truncations in the topology of the weighted absolute sums.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L545-L547

import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
import Theorems.Thm_RiemannMasullo_mem_rapidDecaySequenceSubmodule_of_finiteSupport
import Theorems.Thm_RiemannMasullo_rapidDecaySequence_withSeminorms
import Mathlib
open RiemannMasullo Set Filter Topology
open scoped ENNReal

namespace RiemannMasullo
theorem rapidDecaySequence_finiteSupport_dense (r : ℕ) :
    Dense {s : RapidDecaySequence r | (Function.support (fun a => s a)).Finite} := by sorry
end RiemannMasullo
