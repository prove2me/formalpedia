-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_ratio_frame_recode
-- name    : QuantumMaxCutEnergy.ratio_frame_recode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-01T17:42:20.788194+00:00
-- url     : https://prove2.me/theorems/6ef61e6d-2911-432b-a32e-441d4cd51e3f
-- title:
--   Bit program recoding the campaign value frame into the library ratio frame
-- statement:
--   There is a polynomial-time Boolean-stack program that reads a nonnegative rational in the campaign's value encoding and writes the same rational in the library's ratio encoding.
--
--   Concretely, `encodeValue q` is the concatenation of the frames of the numerator and the denominator, each frame being the unary length of the binary expansion, a separator, and the binary expansion; the library's `Ratio.encode` is the quoted signed-numerator frame followed by the binary denominator frame. Both encodings are self-delimiting descriptions of the same ordered pair of naturals, so the conversion is a finite-state bit transduction: locate the end of the first frame by reading its unary prefix, copy its binary payload into the signed-integer format, then copy the second payload unchanged. No arithmetic on the represented numbers and no numerical approximation is involved; only copying, counting and the insertion of separator bits.
-- source:
--   Not a quoted paper result. Encoding-conversion step of `QuantumMaxCutEnergy.exists_polyProgram_of_tm2InPolyTime`; the campaign's value frame is `QuantumMaxCutEnergy.encodeValue` (unary-length-prefixed binary naturals, `encodeNumber`) and the library frame is `OAI.MetricKMedian.Binary.Ratio.encode` (`Ratio.parts`/`Ratio.normalized`). Reusable word transducers of the runtime library (`BooleanTransducer`, `BooleanEncoding`, `BooleanRecode`) are the intended tools.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Mathlib
open scoped BigOperators

theorem QuantumMaxCutEnergy.ratio_frame_recode :
    Nonempty (OAI.MetricKMedian.Binary.PolyProgram QuantumMaxCutEnergy.encodeValue
      (fun q : ℚ≥0 => OAI.MetricKMedian.Binary.Ratio.encode (q : ℚ)) id) := by sorry
